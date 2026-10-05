# -*- coding: utf-8 -*-
"""
中文字幕匹配插件（MediaSubMatcher）

扫描 Jellyfin 媒体库，为缺少中文字幕的电影/剧集自动：
1. 通过字幕库（zmk.pw）/ OpenSubtitles / assrt.net 搜索中文字幕
2. 按季集/分辨率/语言挑选最佳匹配
3. 下载解压，按 <视频名>.<标签>.<后缀> 命名落盘到视频同目录
4. 可选 ffsubsync 对齐时间轴（基于视频音轨）
5. 触发 Jellyfin 刷库，字幕即刻可见

边界与红线：
- 只新增字幕文件，不删除、不修改任何媒体文件
- 已有中文字幕（内封或外挂）的项目直接跳过
- 搜不到的不硬凑，只记录日志
"""

import asyncio
import base64
import json
import io
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import zipfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote

import requests
import urllib3

urllib3.disable_warnings()

from app import schemas
from app.core.config import settings
from app.helper.mediaserver import MediaServerHelper
from app.log import logger
from app.plugins import _PluginBase
from app.utils.http import RequestUtils

lock = threading.Lock()
_zmk_ocr = None           # ddddocr 实例（惰性初始化）
_zmk_renew_ts = 0         # 上次自动续期时间戳（60s 内不重复续期）
_os_jwt_ts = 0            # 上次 JWT 获取时间戳
_align_queue = None       # 后台对齐队列（惰性初始化）
_align_worker_on = False  # 对齐 worker 已启动标记
_align_lock = threading.Lock()  # 对齐队列初始化锁
_run_start_ts = 0         # 本次运行开始时间（看门狗用）
_notify_lock = threading.Lock()  # 事件汇总缓冲锁（对齐 worker 线程与主流程并发写）

# 字幕文件后缀（可落盘的文本字幕）
SUB_EXTS = {".srt", ".ass", ".ssa"}
# 可对齐的后缀（ffsubsync 对 srt/ass 都能对齐，且实测保留 ASS 的 [V4+ Styles] 与全部对话）
ALIGNABLE_EXTS = {".srt", ".ass"}
# 压缩包后缀
ARCHIVE_EXTS = {".zip"}

# 中文标记（用于判定字幕语言）
CN_MARKERS = ["简", "繁", "中字", "中文", "chs", "cht", "zh", "gb", "big5", "sc&tc", "sc", "tc"]
# 中文内封字幕轨的 Language 取值
CN_LANGS = {"chi", "zho", "zh", "zh-cn", "zh-sg", "zh-hans", "zh-tw", "zh-hk", "zh-hant", "chs", "cht"}
# 内封轨标题标记
CN_STREAM_MARKERS = ["chs", "cht", "简", "繁", "中文", "zh"]


def _has_cn_text(text: str) -> bool:
    if not text:
        return False
    low = text.lower()
    return any(m.lower() in low for m in CN_MARKERS)


def _detect_resolution(text: str) -> Optional[str]:
    if not text:
        return None
    m = re.search(r"(2160p|1080p|720p)", text, re.I)
    return m.group(1).lower() if m else None


def _parse_season_episode(text: str) -> Tuple[Optional[int], List[int]]:
    """从文本中解析季号与集号列表"""
    season, eps = None, []
    if not text:
        return season, eps
    m = re.search(r"[sS](\d{1,2})[\s._-]*(?:[eE][xX]?(\d{1,3}))?", text)
    if m and m.group(1):
        season = int(m.group(1))
    for em in re.finditer(r"[eE][xX]?[pP]?(\d{1,3})", text):
        eps.append(int(em.group(1)))
    if not eps:
        for cm in re.finditer(r"第\s*(\d{1,3})\s*[集话話]", text):
            eps.append(int(cm.group(1)))
    return season, eps


def _wb_esc(text) -> str:
    """汇总消息里的 HTML 转义（文件名可能含 & < >）"""
    return (str(text or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def _wb_push(title, content):
    """把消息推送到 PushPlus（后台线程，失败静默）。

    v1.3.0 起本函数只由 _notify_flush() 调用一次/轮，不再是逐条事件推送。
    """
    def _w():
        try:
            tk = ""
            try:
                with open("/config/.pushplus_token", encoding="utf-8") as f:
                    tk = f.read().strip()
            except Exception:
                pass
            if not tk:
                return
            import json as _j
            import urllib.request as _u
            payload = {"token": tk, "title": title, "content": content, "template": "html"}
            req = _u.Request(
                "https://www.pushplus.plus/send",
                data=_j.dumps(payload, ensure_ascii=False).encode("utf-8"),
                headers={"Content-Type": "application/json"},
            )
            _u.urlopen(req, timeout=15)
        except Exception:
            pass
    try:
        import threading as _t
        _t.Thread(target=_w, daemon=True).start()
    except Exception:
        pass



class MediaSubMatcher(_PluginBase):
    # 插件名称
    plugin_name = "中文字幕匹配"
    # 插件描述
    plugin_desc = "扫描Jellyfin媒体库，为缺少中文字幕的电影/剧集自动搜索下载中文字幕并落盘，可选ffsubsync对齐时间轴。已有中文字幕的自动跳过。"
    # 插件图标
    plugin_icon = "https://raw.githubusercontent.com/jxxghp/MoviePilot-Plugins/main/icons/substrata.png"
    # 插件版本
    plugin_version = "1.3.0"
    # 插件作者
    plugin_author = "leon"
    # 作者主页
    author_url = ""
    # 插件配置项ID前缀
    plugin_config_prefix = "mediasubmatcher_"
    # 加载顺序
    plugin_order = 20
    # 可使用的用户级别
    auth_level = 1

    _enabled = False
    _interval = 6
    _max_keywords = 10
    _align = True
    _lang_tag = "chs"
    _exclude_paths = ""
    _notify = False

    def init_plugin(self, config: dict = None):
        if config:
            self._enabled = bool(config.get("enabled"))
            try:
                self._interval = max(int(config.get("interval") or 6), 1)
            except (TypeError, ValueError):
                self._interval = 6
            try:
                self._max_keywords = max(int(config.get("max_keywords") or 10), 1)
            except (TypeError, ValueError):
                self._max_keywords = 10
            self._align = bool(config.get("align"))
            # 注意：Jellyfin 不识别 .chs 标签（会显示"未定义"），用 ISO 639-1 的 zh
            self._lang_tag = (config.get("lang_tag") or "zh").strip(". ") or "zh"
            self._exclude_paths = config.get("exclude_paths") or ""
            self._notify = bool(config.get("notify"))
            self._os_api_key = (config.get("os_api_key") or "").strip()
            self._os_username = (config.get("os_username") or "").strip()
            self._os_password = (config.get("os_password") or "").strip()
            self._assrt_token = (config.get("assrt_token") or "").strip()
            self._os_jwt = (self._fget("os_jwt") or "").strip()
            # 恢复 JWT 签发时间，避免每次下载都重复登录
            global _os_jwt_ts
            try:
                _os_jwt_ts = float(self._fget("os_jwt_ts") or 0)
            except (TypeError, ValueError):
                _os_jwt_ts = 0
            self._zmk_cookies = (config.get("zmk_cookies") or "").strip()
            if not self._zmk_cookies:
                # 配置为空时回退到自动续期保存的 Cookie（跨重启保持）
                try:
                    self._zmk_cookies = (self._fget("zmk_cookies") or "").strip()
                except Exception:
                    pass
            self._page_scan_enabled = bool(config.get("page_scan_enabled", True))
            try:
                self._page_scan_count = max(int(config.get("page_scan_count") or 10), 1)
            except (TypeError, ValueError):
                self._page_scan_count = 10
            try:
                self._page_scan_daily_cap = max(int(config.get("page_scan_daily_cap") or 40), 1)
            except (TypeError, ValueError):
                self._page_scan_daily_cap = 40
            # 历史字幕分批补对齐
            self._realign_enabled = bool(config.get("realign_enabled", True))
            try:
                self._realign_per_run = max(int(config.get("realign_per_run") or 30), 1)
            except (TypeError, ValueError):
                self._realign_per_run = 30
            # 重启后继续处理遗留的后台对齐任务
            try:
                for item in (self._fget("align_pending") or []):
                    self._enqueue_align(item.get("video") or "", item.get("sub") or "")
            except Exception:
                pass

        # 一次性迁移：history 原先为降序（最新在前），现统一为升序（最新在末尾）。
        # 原因：MP 面板的"插件处理历史"显示的是数组后 N 条，降序会让新记录永远落在窗口外。
        try:
            hist = self.get_data("history") or []
            if len(hist) > 1:
                t_first = str((hist[0] or {}).get("time") or "")
                t_last = str((hist[-1] or {}).get("time") or "")
                if t_first > t_last:
                    hist.reverse()
                    self.save_data("history", hist)
                    logger.info(f"{self.plugin_name} history 顺序已迁移为升序（最新在末尾）")
        except Exception:
            pass

    @staticmethod
    def get_command() -> List[Dict[str, Any]]:
        pass

    def get_api(self) -> List[Dict[str, Any]]:
        return [
            {
                "path": "/run_now",
                "endpoint": self.run_now_api,
                "methods": ["GET"],
                "summary": "立即执行中文字幕匹配",
            },
            {
                "path": "/search_test",
                "endpoint": self.search_test_api,
                "methods": ["GET"],
                "summary": "调试：测试关键词的字幕搜索结果",
            },
            {
                "path": "/match_test",
                "endpoint": self.match_test_api,
                "methods": ["GET"],
                "summary": "调试：对指定Jellyfin条目跑完整匹配流程（搜索→下载→落盘→对齐）",
            },
            {
                "path": "/attach",
                "endpoint": self.attach_api,
                "methods": ["GET"],
                "summary": "外部挂载字幕：读 plan.json 逐条对齐+落盘（8791 手动挂载面板调用）",
            },
        ]

    def search_test_api(self, keyword: str = "", apikey: str = ""):
        if apikey != settings.API_TOKEN:
            return schemas.Response(success=False, message="API密钥错误")
        if not keyword:
            return schemas.Response(success=False, message="缺少keyword参数")
        subs = self._search_subtitles(keyword)
        samples = [
            {
                "title": s.title,
                "site": s.site_name,
                "language": s.language,
                "season_episode": getattr(s, "season_episode", None),
                "file_name": s.file_name,
            }
            for s in subs[:10]
        ]
        return schemas.Response(
            success=True,
            message=f"关键词[{keyword}]共 {len(subs)} 条结果",
            data=samples,
        )

    def match_test_api(self, item_id: str = "", apikey: str = ""):
        """
        调试：对单个 Jellyfin 条目跑完整流程，返回每一步细节（真实落盘）
        """
        if apikey != settings.API_TOKEN:
            return schemas.Response(success=False, message="API密钥错误")
        if not item_id:
            return schemas.Response(success=False, message="缺少item_id参数")
        jellyfin = self._get_jellyfin()
        if not jellyfin:
            return schemas.Response(success=False, message="未找到Jellyfin实例")
        res = jellyfin.get_data(
            f"[HOST]Items?Ids={item_id}&Fields=Path,MediaStreams,ProductionYear,"
            "OriginalTitle,ParentIndexNumber,IndexNumber,SeriesName&api_key=[APIKEY]"
        )
        if not res or res.status_code != 200:
            return schemas.Response(success=False, message="Jellyfin条目查询失败")
        raw = (res.json().get("Items") or [None])[0]
        if not raw:
            return schemas.Response(success=False, message="条目不存在")
        item = {
            "id": raw.get("Id"),
            "type": "movie" if raw.get("Type") == "Movie" else "episode",
            "name": raw.get("Name") or "",
            "original": raw.get("OriginalTitle") or "",
            "year": raw.get("ProductionYear") or "",
            "path": self._to_local_path(raw.get("Path") or "") or raw.get("Path") or "",
            "streams": raw.get("MediaStreams") or [],
            "series": raw.get("SeriesName") or "",
            "season": raw.get("ParentIndexNumber"),
            "episode": raw.get("IndexNumber"),
        }
        local = self._to_local_path(item["path"])
        report = {"item": item["name"], "path": local, "type": item["type"]}
        if not local:
            return schemas.Response(success=False, message=f"路径不在/media/sata下：{item['path']}")
        report["has_chinese"] = self._has_chinese_subtitle(item, local)
        if item["type"] == "movie":
            report["processed"] = self._process_movie(item)
        else:
            report["processed"] = self._process_series(
                item["series"] or item["name"], item.get("season") or 1, [item]
            )
        return schemas.Response(success=True, message="执行完成", data=report)

    # ---------------- 外部字幕挂载（8791 手动挂载面板） ----------------

    def attach_api(self, plan: str = "", apikey: str = ""):
        """
        外部挂载字幕：读 plan.json，逐条把字幕落到目标视频同目录并按需对齐。

        plan.json：
          {"align": true, "overwrite": false,
           "items": [{"video": "<Jellyfin原始路径 或 /media/sata 路径>",
                      "sub":   "<MP 容器内可见的字幕绝对路径>"}]}
        """
        if apikey != settings.API_TOKEN:
            return schemas.Response(success=False, message="API密钥错误")
        if not plan:
            return schemas.Response(success=False, message="缺少plan参数")
        plan_file = Path(plan)
        if not plan_file.is_file():
            return schemas.Response(success=False, message=f"plan 文件不存在：{plan}")
        try:
            spec = json.loads(plan_file.read_text(encoding="utf-8"))
        except Exception as err:
            return schemas.Response(success=False, message=f"plan 解析失败：{err}")
        items = spec.get("items") or []
        if not items:
            return schemas.Response(success=False, message="plan 内没有 items")
        align = bool(spec.get("align", True))
        overwrite = bool(spec.get("overwrite", False))
        refresh = bool(spec.get("refresh", True))
        # ffsubsync 是外部命令依赖，先确保持久卷 vendor 已进 PATH/PYTHONPATH
        self._ensure_ffs_env()
        results = []
        ok_cnt = 0
        for it in items:
            r = self._attach_one(it, align, overwrite)
            results.append(r)
            if r.get("ok"):
                ok_cnt += 1
        refreshed = False
        if refresh:
            try:
                jellyfin = self._get_jellyfin()
                if jellyfin:
                    jellyfin.refresh_root_library()
                    refreshed = True
            except Exception as err:
                logger.warning(f"{self.plugin_name} 外部挂载后刷库失败：{err}")
        return schemas.Response(
            success=True,
            message=f"共 {len(items)} 条，成功 {ok_cnt}，失败 {len(items) - ok_cnt}",
            data={
                "total": len(items),
                "ok": ok_cnt,
                "failed": len(items) - ok_cnt,
                "refreshed": refreshed,
                "items": results,
            },
        )

    def _attach_one(self, it: dict, align: bool, overwrite: bool) -> Dict[str, Any]:
        """单条外部字幕：定位视频 → 读字幕 → 落盘（可覆盖）+ 对齐"""
        video_raw = str(it.get("video") or "").strip()
        sub_raw = str(it.get("sub") or "").strip()
        if not video_raw or not sub_raw:
            return {"video": video_raw, "sub": sub_raw, "ok": False, "msg": "缺少 video 或 sub"}
        video = self._to_local_path(video_raw)
        if not video and video_raw.startswith("/media/sata"):
            video = video_raw
        if not video:
            return {"video": video_raw, "sub": sub_raw, "ok": False,
                    "msg": f"视频路径不可用：{video_raw}"}
        sub_file = Path(sub_raw)
        if not sub_file.is_file():
            return {"video": video, "sub": sub_raw, "ok": False,
                    "msg": f"字幕文件不存在：{sub_raw}"}
        try:
            content = sub_file.read_bytes()
        except OSError as err:
            return {"video": video, "sub": sub_raw, "ok": False, "msg": f"读取字幕失败：{err}"}
        if not content:
            return {"video": video, "sub": sub_raw, "ok": False, "msg": "字幕内容为空"}
        try:
            saved = self._save_subtitle(video, sub_file.name, content, align, overwrite=overwrite)
        except TypeError:
            # 兼容未打 overwrite 补丁的 _save_subtitle
            saved = self._save_subtitle(video, sub_file.name, content, align)
        if not saved:
            return {"video": video, "sub": sub_raw, "ok": False, "msg": "落盘失败（详见插件日志）"}
        ext = Path(sub_file.name).suffix.lower()
        return {
            "video": video,
            "sub": sub_raw,
            "ok": True,
            "msg": "已挂载" + ("，对齐挂起后台执行" if (align and ext in ALIGNABLE_EXTS) else "（未对齐）"),
        }

    # ---------------- 配置页 ----------------

    def get_form(self) -> Tuple[List[dict], Dict[str, Any]]:
        return [
            {
                "component": "VForm",
                "content": [
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 4},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {"model": "enabled", "label": "启用插件"},
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 4},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {"model": "align", "label": "ffsubsync对齐时间轴（仅.srt）"},
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 4},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {"model": "notify", "label": "发送通知"},
                                    }
                                ],
                            },
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 4},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "interval",
                                            "label": "运行间隔（小时）",
                                            "type": "number",
                                        },
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 4},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "max_keywords",
                                            "label": "每轮最多搜索数",
                                            "type": "number",
                                        },
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 4},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {"model": "lang_tag", "label": "字幕语言标签（落盘命名）"},
                                    }
                                ],
                            },
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12},
                                "content": [
                                    {
                                        "component": "VTextarea",
                                        "props": {
                                            "model": "exclude_paths",
                                            "label": "排除路径",
                                            "rows": 3,
                                            "placeholder": "每行一个路径前缀，如 /media/sata2/动画 会被跳过",
                                        },
                                    }
                                ],
                            }
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {
                                            "model": "page_scan_enabled",
                                            "label": "种子详情页字幕附件扫描",
                                        },
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "page_scan_count",
                                            "label": "每轮详情页数（限速防风控）",
                                            "type": "number",
                                        },
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "page_scan_daily_cap",
                                            "label": "每日详情页总上限",
                                            "type": "number",
                                        },
                                    }
                                ],
                            },
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {
                                            "model": "realign_enabled",
                                            "label": "历史字幕分批补对齐",
                                        },
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "realign_per_run",
                                            "label": "每轮补对齐条数",
                                            "type": "number",
                                        },
                                    }
                                ],
                            },
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "os_api_key",
                                            "label": "OpenSubtitles API Key（可选）",
                                        },
                                    },
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "assrt_token",
                                            "label": "assrt.net API Token（射手网·伪站，可选）",
                                        },
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VTextField",
                                        "props": {
                                            "model": "zmk_cookies",
                                            "label": "字幕库 Cookie（zmk.pw 过墙后粘贴）",
                                        },
                                    }
                                ],
                            },
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12},
                                "content": [
                                    {
                                        "component": "VAlert",
                                        "props": {
                                            "type": "info",
                                            "variant": "tonal",
                                            "text": "扫描Jellyfin电影/剧集，缺中文字幕的自动搜索下载，"
                                                    "字幕源：PT站字幕区 + 字幕库zmk.pw（需过墙Cookie）+ OpenSubtitles（需API Key，可选）。"
                                                    "按 <视频名>.标签.后缀 命名落盘后触发刷库。已有中文字幕（内封或外挂）自动跳过；"
                                                    "视频同目录已有同名字幕文件（无论语言）也跳过，避免重复。搜不到的只记日志。",
                                        },
                                    }
                                ],
                            }
                        ],
                    },
                ],
            }
        ], {
            "enabled": False,
            "align": True,
            "notify": False,
            "interval": 6,
            "max_keywords": 10,
            "lang_tag": "zh",
            "exclude_paths": "",
            "os_api_key": "",
            "assrt_token": "",
            "page_scan_enabled": True,
            "page_scan_count": 10,
            "page_scan_daily_cap": 40,
            "realign_enabled": True,
            "realign_per_run": 30,
        }

    def get_page(self) -> List[dict]:
        last_run = self.get_data("last_run") or {}
        history = self.get_data("history") or []
        lines = []
        # history 现在按时间正序存放（最新在末尾），展示时取最后 30 条并倒序
        for h in list(reversed(history[-30:])):
            lines.append(h.get("text") or "")
        # 对齐累计统计：面板通用历史组件只显示固定窗口，这里直接给出总账
        tot = self._fget("align_stats_total") or {}
        t_ok, t_fail = int(tot.get("ok") or 0), int(tot.get("fail") or 0)
        align_txt = "暂无对齐记录"
        if t_ok or t_fail:
            align_txt = f"已对齐 {t_ok} 条"
            if t_fail:
                align_txt += f"，{t_fail} 条无法对齐（保留原字幕）"
        # v1.3.0 事件汇总：待推送缓冲 + 上次推送时间
        try:
            pending_n = len(self._fget("notify_pending") or [])
        except Exception:
            pending_n = 0
        try:
            _last_push = float(self._fget("notify_last_ts") or 0)
        except (TypeError, ValueError):
            _last_push = 0
        push_txt = ("上次汇总推送：" + time.strftime("%m-%d %H:%M", time.localtime(_last_push))) \
            if _last_push else "尚未汇总推送"
        notify_txt = (f"待汇总事件 {pending_n} 条｜{push_txt}｜"
                      f"按“发送通知”开关，每轮扫描（{self._interval}h）汇总推送一次")
        page = [
            {
                "component": "VRow",
                "content": [
                    {
                        "component": "VCol",
                        "props": {"cols": 12, "md": 8},
                        "content": [
                            {
                                "component": "VBtn",
                                "props": {
                                    "color": "primary",
                                    "text": "立即扫描匹配",
                                },
                                "events": {
                                    "click": {
                                        "api": "plugin/MediaSubMatcher/run_now",
                                        "method": "get",
                                        "params": {
                                            "apikey": settings.API_TOKEN
                                        },
                                    }
                                },
                            }
                        ],
                    },
                    {
                        "component": "VCol",
                        "props": {"cols": 12, "md": 4},
                        "content": [
                            {
                                "component": "VCardText",
                                "props": {
                                    "class": "text-right",
                                    "text": f"上次运行：{last_run.get('time', '-')}｜{last_run.get('summary', '尚未运行')}",
                                },
                            }
                        ],
                    },
                ],
            },
            {
                "component": "VRow",
                "content": [
                    {
                        "component": "VCol",
                        "props": {"cols": 12},
                        "content": [
                            {
                                "component": "VAlert",
                                "props": {
                                    "type": "info",
                                    "variant": "tonal",
                                    "text": "时间轴对齐累计 — " + align_txt,
                                },
                            }
                        ],
                    }
                ],
            },
            {
                "component": "VRow",
                "content": [
                    {
                        "component": "VCol",
                        "props": {"cols": 12},
                        "content": [
                            {
                                "component": "VAlert",
                                "props": {
                                    "type": "success",
                                    "variant": "tonal",
                                    "text": "通知方式（v1.3.0）— " + notify_txt,
                                },
                            }
                        ],
                    }
                ],
            },
            {
                "component": "VRow",
                "content": [
                    {
                        "component": "VCol",
                        "props": {"cols": 12},
                        "content": [
                            {
                                "component": "VTextarea",
                                "props": {
                                    "readonly": True,
                                    "rows": 14,
                                    "label": "最近处理记录",
                                    "model-value": "\n".join(lines) or "暂无记录",
                                },
                            }
                        ],
                    }
                ],
            },
        ]
        return page

    def get_service(self) -> List[Dict[str, Any]]:
        if self._enabled and self._interval:
            return [
                {
                    "id": "MediaSubMatcher",
                    "name": "中文字幕匹配服务",
                    "trigger": "interval",
                    "func": self.run_task,
                    "kwargs": {"hours": self._interval},
                }
            ]
        return []

    def stop_service(self):
        pass

    def get_state(self) -> bool:
        return self._enabled

    # ---------------- API 入口 ----------------

    def run_now_api(self, apikey: str = ""):
        if apikey != settings.API_TOKEN:
            return schemas.Response(success=False, message="API密钥错误")
        if not self._enabled:
            return schemas.Response(success=False, message="插件未启用，请先在配置中启用")
        started = self.start_background()
        if not started:
            return schemas.Response(success=False, message="已有任务在运行中")
        return schemas.Response(success=True, message="已开始执行中文字幕匹配，结果见插件页面")

    def start_background(self) -> bool:
        global _run_start_ts
        # 看门狗：上次运行超过 45 分钟未结束（线程挂死持锁）则强制重置锁
        if lock.locked() and _run_start_ts and time.time() - _run_start_ts > 45 * 60:
            logger.warning(f"{self.plugin_name} 检测到上次运行超时未结束，强制重置运行锁")
            try:
                lock.release()
            except RuntimeError:
                pass
        if not lock.acquire(blocking=False):
            return False
        _run_start_ts = time.time()
        t = threading.Thread(target=self._locked_run, daemon=True)
        t.start()
        return True

    def _locked_run(self):
        try:
            self.run_task()
        except Exception as err:
            logger.error(f"{self.plugin_name} 运行异常中断：{type(err).__name__}: {err}", exc_info=True)
            try:
                history = self._fget("history") or []
                history.append({
                    "time": time.strftime("%Y-%m-%d %H:%M:%S"),
                    "text": f"运行异常中断：{type(err).__name__}: {err}",
                    "ok": False,
                })
                del history[:-100]
                self._fsave("history", history)
                self._safe_save_data("history", history)
            except Exception:
                pass
        finally:
            lock.release()

    def run_task(self):
        """
        主流程：扫描 → 分组 → 搜索 → 下载 → 落盘 → 刷库
        """
        logger.info(f"{self.plugin_name} 开始运行")
        logger.info(f"{self.plugin_name} [step1] 获取Jellyfin服务实例...")
        self._sidecar_cache = {}  # 目录侧车字幕缓存: dir -> (mtime, [字幕文件名])
        jellyfin = self._get_jellyfin()
        if not jellyfin:
            logger.warning(f"{self.plugin_name} 未找到可用的 Jellyfin 服务实例")
            return
        logger.info(f"{self.plugin_name} [step1] Jellyfin实例获取成功")

        try:
            items = self._fetch_items(jellyfin)
        except Exception as err:
            logger.error(f"{self.plugin_name} 获取Jellyfin媒体库失败：{err}")
            return
        if not items:
            logger.info(f"{self.plugin_name} 媒体库为空或获取失败")
            return
        logger.info(f"{self.plugin_name} [step2] 拉取完成，共 {len(items)} 项（按新增时间从新到旧）")

        # 2.0) 历史字幕分批补对齐（复用本次媒体列表，零额外扫描；后台 worker 串行跑，不阻塞主流程）
        try:
            self._realign_batch([self._to_local_path(it.get("path")) for it in items])
        except Exception as err:
            logger.warning(f"{self.plugin_name} 补对齐批次异常：{err}")

        exclude_prefixes = [
            p.strip().replace("/media/disk", "/media/sata")
            for p in self._exclude_paths.splitlines() if p.strip()
        ]

        # 1) 过滤出缺中文字幕的目标
        targets_movies: List[dict] = []
        targets_eps: Dict[Tuple[str, int], List[dict]] = {}
        skipped = 0
        for it in items:
            path = it.get("path")
            if not path:
                continue
            local = self._to_local_path(path)
            if not local:
                continue
            it["path"] = local  # 换算为MP容器内路径，后续搜索/落盘都用它
            if any(local.startswith(p) for p in exclude_prefixes):
                continue
            if self._has_chinese_subtitle(it, local):
                skipped += 1
                continue
            if it["type"] == "movie":
                targets_movies.append(it)
            else:
                key = (it["series"], it.get("season") or 1)
                targets_eps.setdefault(key, []).append(it)

        logger.info(
            f"{self.plugin_name} [step2] 共扫描 {len(items)} 项，已有中文跳过 {skipped}，"
            f"待处理电影 {len(targets_movies)}、剧集组 {len(targets_eps)}"
        )

        # 失败冷却：7天内搜不到的组跳过，避免每轮重复搜同一批；30天后清除记录
        retry_sec = 7 * 86400
        keep_sec = 30 * 86400
        now_ts = time.time()
        failed_map = self.get_data("failed_map") or {}
        for k in [k for k, ts in failed_map.items() if now_ts - ts > keep_sec]:
            failed_map.pop(k, None)

        def cooling(key: str) -> bool:
            ts = failed_map.get(key)
            return ts is not None and (now_ts - ts) < retry_sec

        # 2) 逐组处理（受搜索预算限制）
        searched = 0
        done, failed = 0, 0
        history = self.get_data("history") or []

        def record(text: str, ok: bool):
            nonlocal done, failed
            if ok:
                done += 1
            else:
                failed += 1
            # 按时间正序追加（最新在末尾）：MP 面板的历史组件显示的是数组"后 N 条"，
            # 若用 insert(0) 让最新排头，新记录会永远落在它的显示窗口之外。
            history.append({"time": time.strftime("%Y-%m-%d %H:%M:%S"), "text": text, "ok": ok})
            del history[:-100]

        skipped_cool = 0
        missed_movies, missed_series = [], []
        for movie in targets_movies:
            key = "m:" + movie["path"]
            if cooling(key):
                skipped_cool += 1
                continue
            if searched >= self._max_keywords:
                break
            searched += 1
            ok = self._process_movie(movie)
            if ok:
                failed_map.pop(key, None)
            else:
                failed_map[key] = now_ts
                missed_movies.append(movie)
            record(f"电影[{movie['name']}] {'已匹配中文字幕' if ok else '未找到可用字幕'}", ok)

        for (series, season), eps in targets_eps.items():
            key = f"s:{series}|{season}"
            if cooling(key):
                skipped_cool += 1
                continue
            if searched >= self._max_keywords:
                break
            searched += 1
            ok = self._process_series(series, season, eps)
            if ok:
                failed_map.pop(key, None)
            else:
                failed_map[key] = now_ts
                missed_series.append({"series": series, "season": season, "eps": eps})
            record(
                f"剧集[{series} 第{season}季] {len(eps)}集缺失，{'已匹配' if ok else '未找到可用字幕'}",
                ok,
            )

        self._safe_save_data("failed_map", failed_map)
        if skipped_cool:
            logger.info(f"{self.plugin_name} [step3] 冷却期跳过 {skipped_cool} 组（7天内已搜索失败，稍后重试）")

        # 2.5) 第四源：种子详情页字幕附件（限速扫描，覆盖全部缺失组——含冷却跳过的，最新优先，已扫的不重复）
        if self._page_scan_enabled and (targets_movies or targets_eps):
            try:
                series_groups = [{"series": s, "season": se, "eps": eps}
                                 for (s, se), eps in targets_eps.items()]
                pg_done = self._scan_torrent_pages(targets_movies, series_groups)
                if pg_done:
                    done += pg_done
            except Exception as err:
                logger.error(f"{self.plugin_name} 种子页扫描异常：{err}")

        # 3) 刷库 + 通知
        if done > 0:
            try:
                jellyfin.refresh_root_library()
            except Exception as err:
                logger.warning(f"{self.plugin_name} 触发Jellyfin刷库失败：{err}")

        # 对齐汇总：每轮写一条面板历史，让对齐工作量可见（不计入搜索成功数）
        try:
            align_txt = self._align_summary_text()
            if align_txt:
                history.append({
                    "time": time.strftime("%Y-%m-%d %H:%M:%S"),
                    "text": align_txt,
                    "ok": True,
                })
                del history[:-100]
        except Exception as err:
            logger.warning(f"{self.plugin_name} 对齐汇总写入失败：{err}")

        summary = f"搜索{searched}组，成功{done}，未匹配{failed}"
        self._safe_save_data("last_run", {
            "time": time.strftime("%Y-%m-%d %H:%M:%S"),
            "summary": summary,
        })
        self._safe_save_data("history", history)
        # v1.3.0：取消「每轮摘要单独推 + 逐条事件推」，改为
        # 本轮摘要并入事件缓冲，与匹配/对齐/拦截事件一起汇总成一条推送
        # （配合 interval=6h 的扫描节奏 → 每天约 4 条；5h 最小间隔防止手动扫描多发）
        if searched > 0:
            self._notify_add("run", summary)
        self._notify_flush()
        logger.info(f"{self.plugin_name} 运行完成：{summary}")

    # ---------------- Jellyfin ----------------

    def _get_jellyfin(self):
        """
        获取 Jellyfin 实例（鸭子类型判断）
        """
        services = MediaServerHelper().get_services()
        for name, info in (services or {}).items():
            instance = getattr(info, "instance", None)
            if instance is None:
                continue
            if hasattr(instance, "get_jellyfin_folders"):
                if instance.is_inactive():
                    logger.warning(f"{self.plugin_name} Jellyfin [{name}] 未连接")
                    continue
                logger.info(f"{self.plugin_name} [step1] 使用Jellyfin实例：{name}")
                return instance
        logger.warning(f"{self.plugin_name} [step1] 服务列表中无可用Jellyfin：{list((services or {}).keys())}")
        return None

    def _fetch_items(self, jellyfin) -> List[dict]:
        """
        分页获取全部电影和剧集集（含 Path 与 MediaStreams）
        排序：DateCreated 降序 → 处理顺序即最新到最老
        """
        items: List[dict] = []
        page_size = 500
        start = 0
        max_pages = 200
        page_no = 0
        while True:
            page_no += 1
            if page_no > max_pages:
                logger.warning(f"{self.plugin_name} [step2] 达到分页上限 {max_pages}，停止拉取")
                break
            url = (
                "[HOST]Items?IncludeItemTypes=Movie,Episode&Recursive=true"
                f"&Fields=Path,MediaStreams,ProductionYear,OriginalTitle,ParentIndexNumber,IndexNumber"
                f"&StartIndex={start}&Limit={page_size}"
                "&SortBy=DateCreated&SortOrder=Descending&api_key=[APIKEY]"
            )
            t0 = time.time()
            res = jellyfin.get_data(url)
            dt = round(time.time() - t0, 1)
            if not res or res.status_code != 200:
                logger.warning(
                    f"{self.plugin_name} [step2] 第{page_no}页请求失败（{dt}s，"
                    f"res={'None' if res is None else res.status_code}），停止拉取"
                )
                break
            raw = res.json().get("Items") or []
            for it in raw:
                item = {
                    "id": it.get("Id"),
                    "type": "movie" if it.get("Type") == "Movie" else "episode",
                    "name": it.get("Name") or "",
                    "original": it.get("OriginalTitle") or "",
                    "year": it.get("ProductionYear") or "",
                    "path": it.get("Path") or "",
                    "streams": it.get("MediaStreams") or [],
                    "series": it.get("SeriesName") or "",
                    "season": it.get("ParentIndexNumber"),
                    "episode": it.get("IndexNumber"),
                }
                if item["path"]:
                    items.append(item)
            logger.info(
                f"{self.plugin_name} [step2] 第{page_no}页 {dt}s，本页 {len(raw)} 项，累计 {len(items)}"
            )
            if len(raw) < page_size:
                break
            start += page_size
        return items

    @staticmethod
    def _to_local_path(jf_path: str) -> Optional[str]:
        """
        Jellyfin 路径(/media/diskN/...) → MP 容器内路径(/media/sataN/...)
        """
        if not jf_path:
            return None
        p = jf_path.replace("/media/disk", "/media/sata")
        if p.startswith("/media/sata"):
            return p
        return None

    def _has_chinese_subtitle(self, item: dict, local_path: str) -> bool:
        if not hasattr(self, "_sidecar_cache"):
            self._sidecar_cache = {}  # 惰性初始化（match_test 等直调路径）
        """
        判定是否已有中文字幕：内封中文字幕轨 或 同目录已有同名字幕文件（保守跳过）
        """
        for s in item.get("streams") or []:
            if s.get("Type") != "Subtitle":
                continue
            lang = (s.get("Language") or "").lower()
            title = f"{s.get('Title') or ''} {s.get('DisplayTitle') or ''}"
            if lang in CN_LANGS or _has_cn_text(title):
                return True
        # 同目录侧车字幕：只要同名（同 stem）字幕文件存在就跳过，避免重复落盘
        # 目录级缓存：同一剧集目录几十集共享一次目录扫描（目录 mtime 变化才重扫）
        video = Path(local_path)
        stem = video.stem
        d = video.parent
        key = str(d)
        try:
            mtime = d.stat().st_mtime
        except OSError:
            return False
        cached = self._sidecar_cache.get(key)
        if cached is None or cached[0] != mtime:
            try:
                names = [f.name for f in d.iterdir()
                         if f.is_file() and f.suffix.lower() in SUB_EXTS]
            except OSError:
                names = []
            cached = (mtime, names)
            self._sidecar_cache[key] = cached
        return any(n == stem or n.startswith(stem + ".") for n in cached[1])

    # ---------------- 后台对齐（异步） ----------------

    # 可抽音轨的视频文件后缀（原盘目录/ISO 无单文件音轨）
    _VIDEO_EXTS = {".mkv", ".mp4", ".ts", ".avi", ".wmv", ".m2ts", ".mov", ".mpg"}

    def _bump_align_stat(self, key: str):
        """累加对齐计数（done/fail=新匹配，rdone/rfail=历史补对齐），供每轮写面板汇总"""
        try:
            with _align_lock:
                st = self._fget("align_stats") or {}
                st[key] = int(st.get(key) or 0) + 1
                self._fsave("align_stats", st)
        except Exception:
            pass

    def _align_summary_text(self) -> str:
        """取走并清空本轮对齐统计，返回可写入面板历史的汇总文本（无内容返回空串）"""
        try:
            st = self._fget("align_stats") or {}
        except Exception:
            return ""
        d, f = int(st.get("done") or 0), int(st.get("fail") or 0)
        rd, rf = int(st.get("rdone") or 0), int(st.get("rfail") or 0)
        if not (d or f or rd or rf):
            return ""
        parts = []
        if d or f:
            parts.append(f"新匹配字幕对齐 {d} 条成功" + (f"、{f} 条无法对齐（保留原字幕）" if f else ""))
        if rd or rf:
            parts.append(f"历史字幕补对齐 {rd} 条成功" + (f"、{rf} 条无法对齐" if rf else ""))
        # 累加到累计统计（插件页面直接展示总账，不受面板历史窗口限制）
        try:
            tot = self._fget("align_stats_total") or {}
            tot["ok"] = int(tot.get("ok") or 0) + d + rd
            tot["fail"] = int(tot.get("fail") or 0) + f + rf
            self._fsave("align_stats_total", tot)
        except Exception:
            pass
        self._fsave("align_stats", {})
        return "时间轴对齐 — " + "；".join(parts)

    def _realign_batch(self, paths: List[Optional[str]]) -> int:
        """
        历史字幕分批补对齐：
        挑出同目录已有「<视频名>.<语言标签>.<后缀>」的项，每轮最多排 realign_per_run 条，
        已处理过的记入 realign_done 不再重复。ffsubsync 在后台 worker 串行跑，不阻塞主流程。
        """
        if not self._realign_enabled:
            return 0
        done = self._fget("realign_done") or {}
        queued = 0
        for raw in paths:
            if queued >= self._realign_per_run:
                break
            if not raw:
                continue
            try:
                v = Path(raw)
                if v.is_dir() or v.suffix.lower() not in self._VIDEO_EXTS:
                    continue
                sub = None
                for ext in (".srt", ".ass"):
                    cand = v.parent / f"{v.stem}.{self._lang_tag}{ext}"
                    if cand.exists():
                        sub = cand
                        break
                if sub is None:
                    continue
                key = str(sub)
                if key in done:
                    continue
                self._enqueue_align(str(v), key, quiet=True, realign=True)
                done[key] = time.time()
                queued += 1
            except Exception:
                continue
        if queued:
            # 记录上限 3000 条，超出按时间淘汰最早的，防长期无限增长
            if len(done) > 3000:
                for k in sorted(done, key=lambda x: done.get(x) or 0)[: len(done) - 3000]:
                    done.pop(k, None)
            self._fsave("realign_done", done)
            logger.info(f"{self.plugin_name} [补对齐] 本轮排队 {queued} 条历史字幕（累计已处理 {len(done)}）")
        return queued

    def _enqueue_align(self, video_path: str, sub_path: str, quiet: bool = False,
                       realign: bool = False):
        """对齐任务入队并持久化（MP 重启后 init_plugin 会重新入队）"""
        global _align_queue, _align_worker_on
        import queue
        entry = {"video": video_path, "sub": sub_path}
        if realign:
            entry["realign"] = True
        try:
            pending = self._fget("align_pending") or []
            if entry not in pending:
                pending.append(entry)
                self._fsave("align_pending", pending)
        except Exception:
            pass
        with _align_lock:
            if _align_queue is None:
                _align_queue = queue.Queue()
            _align_queue.put(entry)
        # 按线程名去重：插件重载会重置模块级标志，用线程名判断可避免重复启动 worker
        if not any(t.name == "msm-align-worker" for t in threading.enumerate()):
            threading.Thread(target=self._align_worker_loop, daemon=True,
                             name="msm-align-worker").start()
        _align_worker_on = True
        if not quiet:
            logger.info(f"{self.plugin_name} 对齐任务已挂起后台：{Path(sub_path).name}")

    def _align_worker_loop(self):
        import queue
        global _align_queue
        while True:
            try:
                item = _align_queue.get(timeout=10)
            except Exception:
                continue
            video, sub = item.get("video"), item.get("sub")
            if not video or not sub or not os.path.exists(sub):
                continue
            # 输出文件必须保留字幕扩展名（ffsubsync 靠扩展名判输出格式，
            # 用 .aligning 结尾会抛 NotImplementedError: unsupported output format）
            tmp = sub + ".aligned" + Path(sub).suffix
            try:
                self._ensure_ffs_env()
                ff = shutil.which("ffsubsync")
                cmd = [ff] if ff else ["python", "-m", "ffsubsync"]
                cmd += [video, "-i", sub, "-o", tmp]
                proc = subprocess.run(cmd, capture_output=True, timeout=1800)
                if proc.returncode == 0 and os.path.exists(tmp) and os.path.getsize(tmp) > 100:
                    level, qmsg = self._ffsubsync_quality_check(
                        (proc.stdout or b"").decode("utf-8", "replace"),
                        Path(tmp), self._video_duration(video))
                    if level in ("fail", "warn"):
                        os.remove(tmp)
                        logger.warning(f"{self.plugin_name} 后台对齐产物质量未达标（保留原字幕）：{Path(sub).name} | {qmsg}")
                        self._notify_add("align", Path(sub).name,
                                         f"⚠️ 对齐质量未达标（保留原字幕）：{qmsg}")
                        self._bump_align_stat("rfail" if item.get("realign") else "fail")
                    else:
                        os.replace(tmp, sub)
                        logger.info(f"{self.plugin_name} 后台对齐完成：{Path(sub).name}")
                        self._notify_add("align", Path(sub).name, "✅ 对齐完成")
                        self._bump_align_stat("rdone" if item.get("realign") else "done")
                else:
                    tail = " ".join((proc.stderr or b"").decode("utf-8", "replace").split())[-260:]
                    logger.warning(f"{self.plugin_name} 后台对齐失败（保留原字幕）：{Path(sub).name} | ret={proc.returncode} | {tail}")
                    self._notify_add("align", Path(sub).name,
                                     f"⚠️ 对齐失败（保留原字幕）ret={proc.returncode}")
                    self._bump_align_stat("rfail" if item.get("realign") else "fail")
                    if os.path.exists(tmp):
                        os.remove(tmp)
            except Exception as err:
                logger.warning(f"{self.plugin_name} 后台对齐异常：{err}")
                if os.path.exists(tmp):
                    try:
                        os.remove(tmp)
                    except OSError:
                        pass
            finally:
                try:
                    pending = [p for p in (self._fget("align_pending") or [])
                               if not (p.get("video") == video and p.get("sub") == sub)]
                    self._fsave("align_pending", pending)
                except Exception:
                    pass

    # ---------------- 插件数据文件存储（绕开跨线程 save_data 死锁） ----------------

    def _pdata_file(self, key: str) -> Path:
        try:
            base = self.get_data_path()
        except Exception:
            base = "/config/plugins_data/mediasubmatcher"
        p = Path(str(base))
        try:
            p.mkdir(parents=True, exist_ok=True)
        except OSError:
            p = Path("/tmp/mediasubmatcher")
            p.mkdir(parents=True, exist_ok=True)
        return p / f"{key}.json"

    def _fget(self, key: str, default: Any = None) -> Any:
        try:
            f = self._pdata_file(key)
            if f.exists():
                return json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            pass
        return default

    def _fsave(self, key: str, data: Any):
        try:
            f = self._pdata_file(key)
            f.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        except Exception as err:
            logger.warning(f"{self.plugin_name} 数据文件写入失败[{key}]：{err}")

    def _safe_save_data(self, key: str, value: Any, timeout: int = 10):
        """带超时的 save_data：MP 插件数据接口偶发跨线程死锁，超时放弃（数据已存本地文件）"""
        def _do():
            try:
                self.save_data(key, value)
            except Exception:
                pass
        t = threading.Thread(target=_do, daemon=True)
        t.start()
        t.join(timeout)
        if t.is_alive():
            logger.warning(f"{self.plugin_name} save_data[{key}] 超时放弃（数据已存本地文件）")

    # ---------------- 事件汇总通知（v1.3.0） ----------------
    # 变化点：原先「匹配落盘 / 后台对齐完成 / 对齐失败 / 对齐质量不达标 / 正确性拦截」
    #         5 类事件逐条推 PushPlus（实测约 190 条/天），现改为写入缓冲，
    #         每轮扫描结束时汇总成一条推送 → 配合 interval=6h 即每天约 4 条。

    _NOTIFY_MIN_GAP = 5 * 3600   # 两次汇总的最小间隔（< 扫描间隔 6h，保证每轮都能推）
    _NOTIFY_MAX_KEEP = 500       # 缓冲上限（notify 关闭时也不会无限增长）
    _NOTIFY_MAX_ITEMS = 60       # 每个分区最多列出的明细条数（超出只给计数）
    _NOTIFY_SECTIONS = (
        ("match", "✅ 匹配落盘"),
        ("align", "🎬 时间轴对齐"),
        ("block", "⛔ 正确性拦截"),
    )

    def _notify_add(self, kind: str, item: str, note: str = ""):
        """把一条字幕事件写入待推送缓冲（不再逐条推送）。kind 取 match/align/block/run"""
        try:
            with _notify_lock:
                buf = self._fget("notify_pending") or []
                if not isinstance(buf, list):
                    buf = []
                buf.append({
                    "t": time.strftime("%H:%M"),
                    "k": str(kind or "other"),
                    "i": str(item or ""),
                    "n": str(note or ""),
                })
                if len(buf) > self._NOTIFY_MAX_KEEP:
                    del buf[:-self._NOTIFY_MAX_KEEP]
                self._fsave("notify_pending", buf)
        except Exception as err:
            logger.warning(f"{self.plugin_name} 事件缓冲写入失败：{err}")

    def _notify_flush(self, force: bool = False) -> bool:
        """
        把缓冲里的事件汇总成一条 HTML 推送，并清空缓冲。

        节流：两次推送间隔 < _NOTIFY_MIN_GAP（5h）时**不推送、不清缓冲**，
        事件留到下一轮扫描一并汇总 —— 保证每天推送次数 ≈ 24h/扫描间隔。
        受插件配置项「发送通知」(notify) 控制。
        """
        if not self._notify:
            return False
        now = time.time()
        try:
            last = float(self._fget("notify_last_ts") or 0)
        except (TypeError, ValueError):
            last = 0
        if not force and last and (now - last) < self._NOTIFY_MIN_GAP:
            logger.info(
                f"{self.plugin_name} 事件汇总未达推送间隔（{(now - last) / 3600:.1f}h < "
                f"{self._NOTIFY_MIN_GAP / 3600:.0f}h），留到下轮扫描一并汇总"
            )
            return False
        with _notify_lock:
            buf = self._fget("notify_pending") or []
            if not isinstance(buf, list):
                buf = []
            if not buf:
                self._fsave("notify_last_ts", now)
                return False
            # 先清缓冲再推送（推送在子线程发出），避免与并发写入产生重复
            self._fsave("notify_pending", [])
        counts = {}
        for e in buf:
            k = str(e.get("k") or "other")
            counts[k] = counts.get(k, 0) + 1
        head = " ".join(
            f"{label}{counts[kind]}" for kind, label in self._NOTIFY_SECTIONS if counts.get(kind)
        )
        title = f"中文字幕匹配 · {head}" if head else "中文字幕匹配 · 汇总"
        parts = [f"<b>中文字幕匹配 · 事件汇总</b><br>"
                 f"<span style='color:#888'>{time.strftime('%Y-%m-%d %H:%M')}　"
                 f"共 {len(buf)} 条事件</span>"]
        for e in buf:
            if str(e.get("k")) == "run":
                parts.append(f"<br><b>本轮搜索</b>：{_wb_esc(e.get('i'))}")
        for kind, label in self._NOTIFY_SECTIONS:
            items = [e for e in buf if str(e.get("k")) == kind]
            if not items:
                continue
            parts.append(f"<hr><b>{label}（{len(items)}）</b>")
            hidden = len(items) - self._NOTIFY_MAX_ITEMS
            for e in items[-self._NOTIFY_MAX_ITEMS:]:
                note = _wb_esc(e.get("n"))
                line = f"· {_wb_esc(e.get('t'))}　{_wb_esc(e.get('i'))}"
                if note:
                    line += f"　— {note}"
                parts.append(line)
            if hidden > 0:
                parts.append(f"… 另有 {hidden} 条同类事件（明细见插件日志）")
        parts.append("<br><span style='color:#888'>每轮扫描汇总推送一次 · MediaSubMatcher</span>")
        _wb_push(title, "<br>".join(parts))
        self._fsave("notify_last_ts", now)
        logger.info(f"{self.plugin_name} 事件汇总已推送：{title}（{len(buf)} 条）")
        return True

    @staticmethod
    def _valid_sub_content(content: bytes) -> bool:
        """
        字幕内容硬验证：拒绝压缩包本体/二进制；文本需含足够中文字符（防错配防伪装）
        """
        if not content or len(content) < 10:
            return False
        if content[:2] in (b"PK", b"7z") or content[:4] == b"Rar!":
            return False
        text = None
        for enc in ("utf-8-sig", "utf-8", "gb18030"):
            try:
                text = content.decode(enc)
                break
            except (UnicodeDecodeError, LookupError):
                continue
        if text is None:
            return False
        cjk = sum(1 for ch in text if "\u4e00" <= ch <= "\u9fff")
        return cjk >= 5

    # ---------------- 第四源：种子详情页字幕附件 ----------------

    _PAGE_DONE_KEEP = 60 * 86400  # 已抓详情页记录保留 60 天

    def _db_query(self, sql: str, params: tuple = ()) -> list:
        """查询 MP 主库：复制快照到 /tmp 再读（绕开主进程持锁导致的 disk I/O error）"""
        for attempt in range(2):
            try:
                import sqlite3, shutil
                # CONFIG_PATH 是目录（/config），需拼 user.db
                base = Path(str(getattr(settings, "CONFIG_PATH", "/config")))
                if base.is_dir():
                    src_db = str(base / "user.db")
                elif base.suffix == ".db":
                    src_db = str(base)
                else:
                    src_db = "/config/user.db"
                tmp_db = f"/tmp/msm_user_{attempt}.db"
                shutil.copy(src_db, tmp_db)
                for ext in ("-wal", "-shm"):
                    if os.path.exists(src_db + ext):
                        try:
                            shutil.copy(src_db + ext, tmp_db + ext)
                        except OSError:
                            pass
                con = sqlite3.connect(tmp_db)
                try:
                    return con.execute(sql, params).fetchall()
                finally:
                    con.close()
                    for f in (tmp_db, tmp_db + "-wal", tmp_db + "-shm"):
                        if os.path.exists(f):
                            os.remove(f)
            except Exception as err:
                if attempt == 1:
                    logger.error(f"{self.plugin_name} 本地DB快照查询失败：{err}")
                else:
                    time.sleep(1)
        return []

    def _tr_rpc(self, method: str, arguments: dict) -> Optional[dict]:
        """通过 MP 下载器配置直连 TR RPC（409 自动重试）"""
        rows = self._db_query(
            "select value from systemconfig where key='Downloaders'")
        if not rows:
            return None
        try:
            dl_list = json.loads(rows[0][0])
        except Exception:
            return None
        for dl in dl_list or []:
            conf = dl.get("config") or {}
            host = (conf.get("host") or "").strip()
            if "transmission" not in (dl.get("type") or "").lower() and "transmission" not in host.lower():
                continue
            if host and "://" not in host:
                host = "http://" + host
            host = host.rstrip("/")
            apikey = conf.get("apikey") or ""
            auth = None
            if conf.get("username"):
                auth = base64.b64encode(
                    f"{conf.get('username')}:{conf.get('password')}".encode()).decode()
            sid = ""
            for _ in range(3):
                headers = {"X-Transmission-Session-Id": sid, "Content-Type": "application/json"}
                if auth:
                    headers["Authorization"] = "Basic " + auth
                req = requests.post(f"{host}/transmission/rpc",
                                    json={"method": method, "arguments": arguments},
                                    headers=headers, timeout=30, verify=False)
                if req.status_code == 409:
                    sid = req.headers.get("X-Transmission-Session-Id", "")
                    continue
                if req.status_code == 200:
                    return req.json()
                return None
        return None

    def _site_cookie_for(self, url: str) -> Tuple[Optional[str], Optional[str]]:
        """
        按域名从 MP 的 site 表取 cookie / ua。
        只认 MP 站点列表里配置过的域名——TR 历史种子 comment 里可能带着
        早已不用的站（如 ubits.club / hddolby），那些一律不访问。
        """
        rows = self._db_query("select name, domain, cookie, ua from site")
        if rows:
            self._site_cred_cache = [
                (str(d or "").lower().strip(), ck, ua) for _n, d, ck, ua in rows if d
            ]
        creds = getattr(self, "_site_cred_cache", None) or []
        m = re.match(r"https?://([^/]+)", url or "")
        if not m:
            return None, None
        host = m.group(1).lower().split(":")[0]
        best: Optional[Tuple[str, Optional[str], Optional[str]]] = None
        for dom, ck, ua in creds:
            if host == dom or host.endswith("." + dom) or dom.endswith("." + host):
                if best is None or len(dom) > len(best[0]):
                    best = (dom, ck, ua)
        if best and best[1]:
            return best[1], best[2]
        return None, None

    def _scan_torrent_pages(self, missed_movies: List[dict], missed_series: List[dict]) -> int:
        """
        第四源：抓缺失媒体对应种子的详情页，捡页面里的字幕附件。
        安全策略：只扫 MP site 表里配置过的站（其余一律不发请求）、每轮上限 page_scan_count、
        每日总上限 page_scan_daily_cap、请求间隔 3-8s 随机、同站间隔>=30s、
        已抓 URL 记 60 天、403/429 站点当日熔断。
        """
        done_urls = self._fget("page_scan_done") or {}
        now_ts = time.time()
        for u in [u for u, ts in done_urls.items() if now_ts - ts > self._PAGE_DONE_KEEP]:
            done_urls.pop(u, None)
        blocked_sites = set((self._fget("page_scan_blocked") or {}).keys())
        today = time.strftime("%Y-%m-%d")
        blocked_data = self._fget("page_scan_blocked") or {}
        blocked_sites = {s for s, d in blocked_data.items() if d == today}

        # 候选：组代表媒体路径（targets 已按 DateCreated 降序 → 最新优先）
        candidates: List[Tuple[str, dict]] = []
        for m in missed_movies:
            candidates.append(("movie", m))
        for g in missed_series:
            for eps in [g["eps"]]:
                candidates.append(("series", {"series": g["series"], "season": g["season"], "eps": eps}))

        # TR comment 缓存（一次 RPC 拿全部）
        tr = self._tr_rpc("torrent-get", {"fields": ["hashString", "comment"]})
        comments: Dict[str, str] = {}
        if tr:
            for t in (tr.get("arguments") or {}).get("torrents") or []:
                cm = t.get("comment") or ""
                mm = re.search(r"https?://[^\s\"'<>]+", cm)
                if mm:
                    comments[t.get("hashString", "").lower()] = mm.group(0)

        # 下载记录一次性快照进内存（文件名 -> 种子hash），避免逐条连库
        saved = 0
        scanned = 0
        last_site_ts: Dict[str, float] = {}
        # 每日总上限：无论跑几轮，单日详情页访问量封顶（控制风控风险）
        day_stat = self._fget("page_scan_day") or {}
        if day_stat.get("date") != today:
            day_stat = {"date": today, "count": 0}
        remain = max(self._page_scan_daily_cap - int(day_stat.get("count") or 0), 0)
        if remain <= 0:
            logger.info(f"{self.plugin_name} [种子页] 今日已达上限 {self._page_scan_daily_cap} 页，暂停扫描")
            return 0
        scan_limit = min(self._page_scan_count, remain)
        dl_rows = self._db_query("select download_hash, filepath, fullpath from downloadfiles")
        hash_by_name: Dict[str, str] = {}
        for dhash, fp, fullp in dl_rows:
            if not dhash:
                continue
            for p_ in (fp, fullp):
                if p_:
                    hash_by_name[Path(str(p_)).name.lower()] = dhash
        if not hash_by_name:
            logger.warning(f"{self.plugin_name} 下载记录为空或不可读，种子页扫描跳过")
            return 0

        try:
            for kind, group in candidates:
                if scanned >= scan_limit:
                    break
                # 组内代表视频
                if kind == "movie":
                    rep_path = group["path"]
                    eps = [{"id": "movie", "path": group["path"], "episode": None, "resolution": _detect_resolution(rep_path or "")}]
                else:
                    eps = group["eps"]
                    rep_path = (eps[0].get("path") or "") if eps else ""
                stem = Path(rep_path).stem if rep_path else ""
                if not stem:
                    continue
                # 内存匹配下载记录 -> 种子 hash -> 详情页 URL
                page_url = ""
                stem_l = stem.lower()
                for fname, dhash in hash_by_name.items():
                    if stem_l in fname:
                        page_url = comments.get((dhash or "").lower(), "")
                        if page_url:
                            break
                if not page_url or page_url in done_urls:
                    continue
                # 站点熔断 + 同站间隔
                sm = re.match(r"https?://([^/]+)", page_url)
                if not sm:
                    continue
                site = sm.group(1)
                if site in blocked_sites:
                    continue
                # 只扫 MP 站点列表里配置过的站；不在列表的直接跳过（不发请求）
                cookie, ua = self._site_cookie_for(page_url)
                if not cookie:
                    done_urls[page_url] = now_ts  # 记为已处理，避免反复判断
                    continue
                wait = 3 + (hash(page_url) % 50) / 10.0   # 3.0~8.0 秒随机间隔，伪装真人节奏
                last = last_site_ts.get(site, 0)
                if time.time() - last < 30:               # 同站至少 30 秒一次
                    time.sleep(30 - (time.time() - last))
                time.sleep(wait)
                try:
                    r = requests.get(page_url, headers={
                        "User-Agent": ua or "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/126.0",
                        "Cookie": cookie or "",
                        "Referer": page_url,
                    }, timeout=25, verify=False)
                except Exception as err:
                    logger.warning(f"{self.plugin_name} [种子页] {site} 请求失败：{err}")
                    continue
                scanned += 1
                last_site_ts[site] = time.time()
                done_urls[page_url] = now_ts
                day_stat["count"] = int(day_stat.get("count") or 0) + 1
                if r.status_code in (403, 429):
                    blocked_sites.add(site)
                    blocked_data[site] = today
                    self._fsave("page_scan_blocked", blocked_data)
                    logger.warning(f"{self.plugin_name} [种子页] {site} 被-{r.status_code}，该站今日熔断")
                    continue
                if r.status_code != 200:
                    continue
                # 收集字幕附件链接（排除种子下载链接）
                links = re.findall(
                    r'href="([^"]*(?:\.zip|\.rar|\.7z|\.srt|\.ass|\.ssa)(?:\?[^"]*)?)"', r.text, re.I)
                links = [l for l in links if "download.php" not in l][:5]
                if not links:
                    continue
                logger.info(f"{self.plugin_name} [种子页] {site} 发现 {len(links)} 个字幕附件：{page_url[:60]}")
                for link in links:
                    full = link if link.startswith("http") else (
                        page_url.rsplit("/", 1)[0] + "/" + link.lstrip("/"))
                    try:
                        rd = requests.get(full, headers={
                            "User-Agent": ua or "Mozilla/5.0",
                            "Cookie": cookie or "",
                            "Referer": page_url,
                        }, timeout=60, verify=False)
                        if rd.status_code != 200 or not rd.content:
                            continue
                        files = self._extract_sub_files(rd.content, Path(full).name or "page_sub")
                        if not files:
                            continue
                        if kind == "movie":
                            picked = self._pick_best_file(files, None, None, eps[0]["resolution"])
                            if picked and self._save_subtitle(eps[0]["path"], picked[0], picked[1], self._align):
                                saved += 1
                                done_urls[page_url] = now_ts
                                break
                        else:
                            season = group.get("season") or 1
                            for it in group["eps"]:
                                ep_no = it.get("episode")
                                res = _detect_resolution(it.get("path") or "")
                                picked = self._pick_best_file(files, season, ep_no, res)
                                if picked and self._save_subtitle(it["path"], picked[0], picked[1], self._align):
                                    saved += 1
                    except Exception as err:
                        logger.warning(f"{self.plugin_name} [种子页] 附件下载失败：{err}")
        finally:
            self._fsave("page_scan_done", done_urls)
            self._fsave("page_scan_day", day_stat)
        if scanned:
            logger.info(
                f"{self.plugin_name} [种子页] 本轮扫描 {scanned} 个详情页（今日累计 "
                f"{day_stat.get('count')}/{self._page_scan_daily_cap}），补上 {saved} 组字幕"
            )
        return saved

    def _search_subtitles(self, keyword: str) -> List[Any]:
        """
        聚合三源并行：字幕库 zmk.pw + OpenSubtitles + assrt.net（射手网·伪站）
        （MP 站点字幕区已于 2026-09-30 停用：站表 20 站中仅少数站有字幕 indexer 定义，长期有效 0 条）
        """
        logger.info(f"{self.plugin_name} [搜索] {keyword} → 三源并行")
        results: List[Any] = []

        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=3) as ex:
            f2 = ex.submit(self._search_zmk, keyword)
            f3 = ex.submit(self._search_os, keyword)
            f4 = ex.submit(self._search_assrt, keyword)
            zmk = f2.result()
            os_subs = f3.result()
            assrt = f4.result()
        if zmk:
            logger.info(f"{self.plugin_name} 字幕库[{keyword}] 命中 {len(zmk)} 条")
            results.extend(zmk)
        if os_subs:
            logger.info(f"{self.plugin_name} OpenSubtitles[{keyword}] 命中 {len(os_subs)} 条")
            results.extend(os_subs)
        if assrt:
            logger.info(f"{self.plugin_name} assrt[{keyword}] 命中 {len(assrt)} 条")
            results.extend(assrt)
        if not results:
            logger.warning(f"{self.plugin_name} [搜索] {keyword} 三源均无结果")
        return results
    def _zmk_cookie_dict(self) -> Dict[str, str]:
        ck = {}
        for part in (self._zmk_cookies or "").split(";"):
            if "=" in part:
                k, v = part.split("=", 1)
                ck[k.strip()] = v.strip()
        return ck

    def _zmk_request(self, url: str, referer: str = "") -> Optional[requests.Response]:
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36",
            "Accept-Language": "zh-CN,zh;q=0.9",
        }
        if referer:
            headers["Referer"] = referer
        return requests.get(url, headers=headers, cookies=self._zmk_cookie_dict(),
                            timeout=25, verify=False, allow_redirects=True)

    @staticmethod
    def _zmk_blocked(text: str) -> bool:
        return "防火墙" in (text or "") or "security_verify" in (text or "")

    # ---------------- 验证码 OCR：依赖持久化（MP 镜像重建不失效） ----------------

    def _vendor_dir(self, create: bool = False) -> Optional[Path]:
        """
        OCR 依赖的持久卷目录，按 Python 版本分目录。
        放在 /config 卷（插件数据目录）下 → 更新 MP 镜像、重建容器都不会丢。
        """
        try:
            base = Path(str(self.get_data_path())) / "vendor"
        except Exception:
            # MP 的插件数据目录实际为 /config/plugins/<PluginID>
            base = Path("/config/plugins/MediaSubMatcher/vendor")
        v = sys.version_info
        d = base / f"py{v.major}{v.minor}"
        if create:
            try:
                d.mkdir(parents=True, exist_ok=True)
            except OSError as err:
                logger.warning(f"{self.plugin_name} OCR 依赖目录创建失败：{err}")
                return None
        return d

    def _ensure_ffs_env(self) -> None:
        """
        把持久卷 vendor 注入 PATH / PYTHONPATH。
        ffsubsync 属外部命令依赖（shutil.which 调用），_load_ocr 的 sys.path 机制覆盖不到，
        容器重建后须靠这里恢复其可发现性与依赖导入路径。
        """
        try:
            vdir = self._vendor_dir()
            if not vdir or not vdir.is_dir():
                return
            b = vdir / "bin"
            if b.is_dir():
                p = os.environ.get("PATH", "")
                if str(b) not in p.split(os.pathsep):
                    os.environ["PATH"] = str(b) + os.pathsep + p
            pp = os.environ.get("PYTHONPATH", "")
            if str(vdir) not in pp.split(os.pathsep):
                os.environ["PYTHONPATH"] = str(vdir) + (os.pathsep + pp if pp else "")
        except Exception:
            pass

    def _load_ocr(self):
        """
        加载 ddddocr（云锁验证码识别）：
        ① 容器内已装（最快）→ ② 持久卷 vendor → ③ 都没有则后台安装到持久卷
        """
        global _zmk_ocr
        if _zmk_ocr is not None:
            return _zmk_ocr
        # ① 容器环境直接可导入
        try:
            import ddddocr
            _zmk_ocr = ddddocr.DdddOcr(show_ad=False)
            return _zmk_ocr
        except Exception:
            pass
        # ② 持久卷（镜像重建后依赖仍在这里）
        vdir = self._vendor_dir()
        if vdir and vdir.is_dir():
            if str(vdir) not in sys.path:
                sys.path.insert(0, str(vdir))
            try:
                import ddddocr
                _zmk_ocr = ddddocr.DdddOcr(show_ad=False)
                logger.info(f"{self.plugin_name} 验证码 OCR 已从持久卷加载：{vdir}")
                return _zmk_ocr
            except Exception as err:
                logger.warning(f"{self.plugin_name} 持久卷 OCR 加载失败：{err}")
        # ③ 缺失 → 后台装到持久卷（一次性，以后不再需要）
        self._install_ocr_background()
        return None

    def _install_ocr_background(self):
        if any(t.name == "msm-ocr-install" for t in threading.enumerate()):
            return
        threading.Thread(target=self._install_ocr, daemon=True, name="msm-ocr-install").start()

    def _install_ocr(self):
        """把 ddddocr 依赖装到持久卷（约 290MB）：镜像重建后自动恢复，无需人工介入"""
        vdir = self._vendor_dir(create=True)
        if not vdir:
            return
        pip = shutil.which("pip") or "/usr/local/bin/pip"
        try:
            logger.info(f"{self.plugin_name} 开始安装验证码 OCR 依赖到持久卷（约 290MB，首次较慢）...")
            p = subprocess.run(
                [pip, "install", "--target", str(vdir), "--no-cache-dir",
                 "--disable-pip-version-check", "ddddocr"],
                capture_output=True, timeout=1800,
            )
            if p.returncode == 0:
                logger.info(f"{self.plugin_name} OCR 依赖已装入持久卷：{vdir}（自动过墙下轮生效）")
            else:
                tail = " ".join((p.stderr or b"").decode("utf-8", "replace").split())[-300:]
                logger.warning(f"{self.plugin_name} OCR 依赖安装失败：{tail}")
        except Exception as err:
            logger.warning(f"{self.plugin_name} OCR 依赖安装异常：{err}")

    def _zmk_renew_cookie(self) -> bool:
        """
        自动过字幕库云锁防火墙：拉验证码 → ddddocr 识别 → hex 提交 → 更新 Cookie
        """
        global _zmk_renew_ts
        if time.time() - _zmk_renew_ts < 60:
            return False
        _zmk_renew_ts = time.time()
        ocr = self._load_ocr()
        if ocr is None:
            logger.warning(f"{self.plugin_name} 验证码 OCR 暂不可用（已触发依赖自动安装），本轮跳过过墙")
            return False
        try:
            s = requests.Session()
            s.trust_env = False
            s.headers.update({
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36",
                "Accept-Language": "zh-CN,zh;q=0.9",
            })
            r = s.get("https://zmk.pw/", timeout=25, verify=False)
            m = re.search(r'src="data:image/bmp;base64,([^"]+)"', r.text)
            if not m:
                # 站点有间歇性 403 空响应（WAF/限速）：实测连打 8 次约 2 次拿不到验证码图。
                # 重试 2 次（间隔 2s、3s）再判失败，避免整轮搜不到字幕库。
                for _att in range(2):
                    time.sleep(2 + _att)
                    try:
                        _r2 = s.get("https://zmk.pw/", timeout=25, verify=False)
                        m = re.search(r'src="data:image/bmp;base64,([^"]+)"', _r2.text)
                    except Exception:
                        m = None
                    if m:
                        logger.info(f"{self.plugin_name} 字幕库验证码页第 {_att + 2} 次才拿到（站点间歇性 403）")
                        break
            if not m:
                logger.warning(f"{self.plugin_name} 字幕库防火墙页无验证码图片，自动过墙失败")
                return False
            bmp = base64.b64decode(m.group(1))
            code = (ocr.classification(bmp) or "").strip()
            code = re.sub(r"[^0-9a-zA-Z]", "", code)
            if not code:
                logger.warning(f"{self.plugin_name} 验证码识别为空，自动过墙失败（下轮重试）")
                return False
            def to_hex(t: str) -> str:
                return "".join(f"{ord(c):x}" for c in t)
            s.cookies.set("srcurl", to_hex("https://zmk.pw/"), domain="zmk.pw")
            s.get(f"https://zmk.pw/?security_verify_img={to_hex(code)}", timeout=25, verify=False)
            check = s.get("https://zmk.pw/", timeout=25, verify=False)
            if check.status_code == 200 and not self._zmk_blocked(check.text):
                ck = "; ".join(f"{k}={v}" for k, v in s.cookies.get_dict().items())
                self._zmk_cookies = ck
                self.save_data("zmk_cookies", ck)
                # 同步写回插件配置，保证重启后直接用新 Cookie
                try:
                    cfg = self.get_config() or {}
                    if isinstance(cfg, dict):
                        cfg["zmk_cookies"] = ck
                        self.update_config(cfg)
                except Exception:
                    pass
                logger.info(f"{self.plugin_name} 字幕库 Cookie 已自动续期（验证码 {code} 识别通过）")
                return True
            logger.warning(f"{self.plugin_name} 验证码 {code} 未通过，自动过墙失败（下轮重试）")
            return False
        except Exception as err:
            logger.error(f"{self.plugin_name} 字幕库自动过墙异常：{err}")
            return False

    def _search_zmk(self, keyword: str) -> List[Any]:
        """
        字幕库 zmk.pw（zimuku/SrtKu）网页抓取；Cookie 过期时会提示重新过墙
        """
        if not self._zmk_cookies:
            return []
        from types import SimpleNamespace
        out: List[Any] = []
        try:
            r = self._zmk_request("https://zmk.pw/search?q=" + quote(keyword))
            if r is not None and self._zmk_blocked(r.text):
                # 注意：云锁防火墙页是 404 状态码，必须先查 blocked 再查状态码
                if self._zmk_renew_cookie():
                    r = self._zmk_request("https://zmk.pw/search?q=" + quote(keyword))
                else:
                    return []
            if r is None or r.status_code != 200 or self._zmk_blocked(r.text):
                return []
            items = re.findall(r'href="(//zimuku\.org/detail/(\d+)\.html)"[^>]*title="([^"]{3,80})"', r.text)
            seen = set()
            for _, sub_id, title in items[:15]:
                if sub_id in seen:
                    continue
                seen.add(sub_id)
                is_eng = re.search(r"\.(eng|english)\b", title, re.I)
                out.append(SimpleNamespace(
                    title=title,
                    description="",
                    file_name=title,
                    language="" if is_eng else "zh",
                    site_name="字幕库",
                    enclosure=f"zmk:{sub_id}",
                    site_cookie=None,
                    site_ua=None,
                    site_proxy=False,
                    size=0,
                ))
        except Exception as err:
            logger.error(f"{self.plugin_name} 字幕库搜索[{keyword}]失败：{err}")
        return out

    def _download_zmk(self, sub_id: str) -> Optional[bytes]:
        try:
            r1 = self._zmk_request(f"https://zimuku.org/detail/{sub_id}.html", referer="https://zmk.pw/")
            if r1 is not None and self._zmk_blocked(r1.text):
                # 云锁防火墙页是 404 状态码，先查 blocked
                if not self._zmk_renew_cookie():
                    return None
                r1 = self._zmk_request(f"https://zimuku.org/detail/{sub_id}.html", referer="https://zmk.pw/")
            if r1 is None or r1.status_code != 200 or self._zmk_blocked(r1.text):
                return None
            m1 = re.search(r'href="(/dld/\d+\.html)"', r1.text)
            if not m1:
                return None
            r2 = self._zmk_request("https://zimuku.org" + m1.group(1), referer=r1.url)
            if r2 is None or r2.status_code != 200 or self._zmk_blocked(r2.text):
                return None
            m2 = re.search(r'href="(/download/[^"]+)"', r2.text)
            if not m2:
                return None
            r3 = self._zmk_request("https://zimuku.org" + m2.group(1), referer="https://zimuku.org" + m1.group(1))
            if r3 is None or r3.status_code != 200 or not r3.content:
                return None
            return r3.content
        except Exception as err:
            logger.error(f"{self.plugin_name} 字幕库下载异常[{sub_id}]：{err}")
            return None

    def _search_os(self, keyword: str) -> List[Any]:
        """
        OpenSubtitles API（需 API Key，免费档：搜索1000次/天，下载50次/天）
        """
        if not self._os_api_key:
            return []
        # OpenSubtitles 要求查询词 ≥3 字符，否则必返 400 "Query is too short"
        # （2 字中文片名如「沙丘/活着/影」会命中）→ 直接跳过：省一次配额，也不刷误导性错误日志
        if len(keyword.strip()) < 3:
            logger.info(f"{self.plugin_name} OpenSubtitles 跳过[{keyword}]：查询词不足 3 字符（OS 硬限制）")
            return []
        from types import SimpleNamespace
        out: List[Any] = []
        try:
            r = requests.get(
                "https://api.opensubtitles.com/api/v1/subtitles",
                params={"query": keyword, "languages": "zh-cn,zh-tw,zh", "order_by": "points_add"},
                headers={"Api-Key": self._os_api_key, "User-Agent": "MediaSubMatcher v1.0"},
                timeout=25,
            )
            if r.status_code != 200:
                body = (r.text or "")[:120]
                if "too short" in body.lower():
                    logger.info(f"{self.plugin_name} OpenSubtitles 跳过[{keyword}]：查询词过短（{body}）")
                else:
                    logger.warning(f"{self.plugin_name} OpenSubtitles 搜索失败：HTTP {r.status_code} {body}")
                return []
            for it in (r.json().get("data") or [])[:20]:
                attr = it.get("attributes") or {}
                files = attr.get("files") or []
                if not files or not files[0].get("file_id"):
                    continue
                full_name = " ".join(
                    x for x in [attr.get("movie_name") or attr.get("foreign_name") or "",
                                attr.get("release") or "", attr.get("name") or ""] if x
                )
                out.append(SimpleNamespace(
                    title=full_name or f"OS-{files[0]['file_id']}",
                    description=attr.get("comments") or "",
                    file_name=attr.get("file_name") or "",
                    language=attr.get("language") or "",
                    site_name="OpenSubtitles",
                    enclosure=f"osfile:{files[0]['file_id']}",
                    site_cookie=None,
                    site_ua=None,
                    site_proxy=False,
                    size=attr.get("files", [{}])[0].get("size") or 0,
                ))
        except Exception as err:
            logger.error(f"{self.plugin_name} OpenSubtitles 搜索[{keyword}]失败：{err}")
        return out

    def _os_jwt_login(self) -> str:
        """
        用户名密码换 JWT（解锁登录用户下载配额 2000次/24h；匿名仅 5 次/天）
        """
        global _os_jwt_ts
        if self._os_jwt and time.time() - _os_jwt_ts < 20 * 3600:
            return self._os_jwt
        if not (self._os_username and self._os_password):
            return ""
        try:
            r = requests.post(
                "https://api.opensubtitles.com/api/v1/login",
                json={"username": self._os_username, "password": self._os_password},
                headers={"Api-Key": self._os_api_key, "User-Agent": "MediaSubMatcher v1.0",
                         "Content-Type": "application/json", "Accept": "application/json"},
                timeout=25,
            )
            if r.status_code != 200:
                logger.warning(f"{self.plugin_name} OpenSubtitles 登录失败：HTTP {r.status_code} {r.text[:120]}")
                return ""
            token = (r.json() or {}).get("token") or ""
            if token:
                self._os_jwt = token
                _os_jwt_ts = time.time()   # 必须记签发时间，否则每次下载都重新登录
                self._fsave("os_jwt", token)
                self._fsave("os_jwt_ts", _os_jwt_ts)
                logger.info(f"{self.plugin_name} OpenSubtitles JWT 登录成功")
            return token
        except Exception as err:
            logger.error(f"{self.plugin_name} OpenSubtitles 登录异常：{err}")
            return ""

    def _download_os(self, file_id: str) -> Optional[bytes]:
        try:
            headers = {"Api-Key": self._os_api_key, "User-Agent": "MediaSubMatcher v1.0",
                       "Content-Type": "application/json", "Accept": "application/json"}
            jwt = self._os_jwt_login()
            if jwt:
                headers["Authorization"] = f"Bearer {jwt}"
            r = requests.post(
                "https://api.opensubtitles.com/api/v1/download",
                json={"file_id": int(file_id)},
                headers=headers,
                timeout=30,
            )
            if r.status_code != 200:
                logger.warning(f"{self.plugin_name} OpenSubtitles 申请下载链接失败：HTTP {r.status_code} {r.text[:120]}")
                return None
            link = (r.json() or {}).get("link")
            if not link:
                logger.warning(f"{self.plugin_name} OpenSubtitles 未返回下载链接（可能超出免费配额）")
                return None
            # 流式下载 + 总时长硬上限（防慢速滴流服务器挂死主线程）
            r2 = requests.get(link, timeout=(10, 30), stream=True)
            if r2.status_code != 200:
                return None
            chunks, start = [], time.time()
            for chunk in r2.iter_content(65536):
                chunks.append(chunk)
                if time.time() - start > 120:
                    logger.warning(f"{self.plugin_name} OpenSubtitles 下载超120秒中断（防滴流挂死）")
                    return None
            content = b"".join(chunks)
            return content or None
        except Exception as err:
            logger.error(f"{self.plugin_name} OpenSubtitles 下载异常[{file_id}]：{err}")
            return None

    # ---------------- assrt.net（射手网·伪站） ----------------

    _ASSRT_API = "https://api.assrt.net/v1"

    def _assrt_call(self, path: str, **qs):
        """
        调 assrt API。成功返回 JSON dict，失败返回 None。
        注意：免费配额 20 次/分钟（token 与 IP 共享）；下载地址是签名+有时效的，禁止缓存。
        """
        if not self._assrt_token:
            return None
        try:
            params = {"token": self._assrt_token}
            params.update({k: v for k, v in qs.items() if v is not None})
            r = requests.get(
                f"{self._ASSRT_API}/{path}",
                params=params,
                headers={"User-Agent": "MediaSubMatcher v1.0"},
                timeout=25,
            )
            # 鉴权/参数错误时 assrt 返回 400 + JSON，也要解析
            if r.status_code not in (200, 400):
                logger.warning(f"{self.plugin_name} assrt {path} 请求失败：HTTP {r.status_code}")
                return None
            d = r.json() or {}
            if int(d.get("status") or 0) != 0:
                logger.warning(
                    f"{self.plugin_name} assrt {path} 返回错误：status={d.get('status')} {d.get('errmsg')}"
                )
                return None
            return d
        except Exception as err:
            logger.error(f"{self.plugin_name} assrt {path} 异常：{err}")
            return None

    @staticmethod
    def _assrt_is_chinese(item: dict) -> bool:
        """
        判定是否中文字幕。assrt 的 langlist 是**结构化**语言元数据，优先采信：
        只要它明确列了语言却不含中文，就直接排除 —— 避免「其他语言/英语/俄语」字幕
        被落盘成 <视频名>.zh.srt（实测 langoth 的俄字字幕曾通过旧判定）。
        """
        lang = item.get("lang") or {}
        ll = lang.get("langlist") or {}
        if ll.get("langchs") or ll.get("langcht") or ll.get("langdou"):
            return True
        if ll:
            return False
        desc = lang.get("desc") or ""
        return _has_cn_text(desc) or _has_cn_text(item.get("native_name") or "")

    def _search_assrt(self, keyword: str) -> List[Any]:
        """
        assrt.net（射手网·伪站）字幕 API —— 免费、无每日下载上限（仅 20 次/分钟）
        """
        if not self._assrt_token:
            return []
        from types import SimpleNamespace
        out: List[Any] = []
        d = self._assrt_call("sub/search", q=keyword, cnt=15, pos=0)
        if not d:
            return out
        for it in (((d.get("sub") or {}).get("subs")) or []):
            sid = it.get("id")
            if not sid or not self._assrt_is_chinese(it):
                continue
            lang = it.get("lang") or {}
            desc = (lang.get("desc") or "").strip()
            native = (it.get("native_name") or "").replace("/", " ").strip()
            vname = it.get("videoname") or ""
            # title 里必须带中文（_is_chinese_sub / _score_sub 依赖它打分）
            title = f"{native} {desc}".strip() or f"assrt-{sid}"
            out.append(SimpleNamespace(
                title=title,
                description=f"{vname} {it.get('release_site') or ''} vote={it.get('vote_score') or 0}".strip(),
                file_name=vname,
                language=desc or "zh",
                site_name="assrt",
                enclosure=f"assrtfile:{sid}",
                site_cookie=None,
                site_ua=None,
                site_proxy=False,
                size=0,
            ))
        return out

    def _download_assrt(self, sub_id: str):
        """
        取 assrt 字幕内容：优先 filelist 里的**单文件直链**（免解压）；
        没有 filelist 才退回压缩包 url（若为 rar，交给上层内容验证兜底丢弃）
        """
        d = self._assrt_call("sub/detail", id=sub_id)
        if not d:
            return None
        one = ((((d.get("sub") or {}).get("subs")) or [{}]))[0]
        links: List[str] = []
        for f in (one.get("filelist") or []):
            u = f.get("url") or ""
            if u and Path(f.get("f") or "").suffix.lower() in SUB_EXTS:
                links.append(u)
        if not links and one.get("url"):
            links.append(one["url"])
        for link in links[:3]:
            try:
                r2 = requests.get(link, headers={"User-Agent": "MediaSubMatcher v1.0"},
                                  timeout=(10, 30), stream=True)
                if r2.status_code != 200:
                    continue
                chunks, start = [], time.time()
                for chunk in r2.iter_content(65536):
                    chunks.append(chunk)
                    if time.time() - start > 120:
                        logger.warning(f"{self.plugin_name} assrt 下载超120秒中断（防滴流挂死）")
                        return None
                content = b"".join(chunks)
                if content:
                    return content
            except Exception as err:
                logger.warning(f"{self.plugin_name} assrt 直链下载失败（换下一条）：{err}")
        logger.warning(f"{self.plugin_name} assrt 无可用下载直链[{sub_id}]")
        return None

    def _is_chinese_sub(self, sub) -> bool:
        blob = " ".join([sub.title or "", sub.description or "", sub.file_name or "", sub.language or ""])
        return _has_cn_text(blob)

    def _score_sub(self, sub, season: Optional[int], ep: Optional[int], resolution: Optional[str],
                   title_hints: Optional[List[str]] = None) -> Optional[int]:
        """
        给字幕结果打分；返回 None 表示直接排除
        """
        blob = f"{sub.title or ''} {sub.description or ''} {sub.file_name or ''}"
        if not self._is_chinese_sub(sub):
            return None
        # 电影：标题关键词校验（防 OS 模糊匹配错片，如搜"震耳欲聋"混入"震颤"）
        if title_hints and not any(h.lower() in blob.lower() for h in title_hints if h):
            return None
        # 剧集：季集匹配
        if ep is not None:
            sub_season, sub_eps = _parse_season_episode(blob)
            meta = getattr(sub, "meta_info", None)
            if meta is not None:
                m_ep = getattr(meta, "begin_episode", None)
                if m_ep is not None and not sub_eps:
                    sub_eps = [int(m_ep)]
                m_season = getattr(meta, "season", None)
                if m_season is not None and sub_season is None:
                    sub_season = int(m_season)
            if sub_season is not None and season is not None and sub_season != season:
                return None
            if sub_eps and ep not in sub_eps:
                return None
            if sub_season is None and not sub_eps and (season or 1) > 1:
                # 多季剧且字幕未标明季集，宁缺毋滥
                return None
        score = 0
        if _has_cn_text(sub.title or "") and ("简" in (sub.title or "") or "chs" in (sub.title or "").lower()):
            score += 5
        if re.search(r"繁|cht|big5|tc", blob, re.I):
            score += 2
        if resolution:
            sub_res = _detect_resolution(blob)
            if sub_res == resolution:
                score += 3
            elif sub_res:
                score -= 2
        if (getattr(sub, "size", 0) or 0) > 0:
            score += 1
        return score

    def _pick_best(self, subs: List[Any], season, ep, resolution, title_hints: Optional[List[str]] = None) -> Optional[Any]:
        best, best_score = None, -1
        for sub in subs:
            s = self._score_sub(sub, season, ep, resolution, title_hints)
            if s is not None and s > best_score:
                best, best_score = sub, s
        return best

    # ---------------- 下载与落盘 ----------------

    def _download_content(self, sub) -> Optional[bytes]:
        try:
            enc = sub.enclosure or ""
            if enc.startswith("zmk:"):
                return self._download_zmk(enc.split(":", 1)[1])
            if enc.startswith("osfile:"):
                return self._download_os(enc.split(":", 1)[1])
            if enc.startswith("assrtfile:"):
                return self._download_assrt(enc.split(":", 1)[1])
            resp = RequestUtils(ua=sub.site_ua, cookies=sub.site_cookie).get_res(
                sub.enclosure,
                proxies=getattr(settings, "PROXY", None) if getattr(sub, "site_proxy", False) else None,
            )
            if resp is None or resp.status_code != 200:
                logger.warning(f"{self.plugin_name} 字幕下载失败[{sub.title}]：HTTP {getattr(resp, 'status_code', 'N/A')}")
                return None
            return resp.content
        except Exception as err:
            logger.error(f"{self.plugin_name} 字幕下载异常[{sub.title}]：{err}")
            return None

    def _extract_sub_files(self, content: bytes, sub_title: str) -> List[Tuple[str, bytes]]:
        """
        从下载内容中提取字幕文件（zip 或单文件），返回 [(文件名, 内容)]
        每个文件都过内容验证（防错片：如 RAR 伪装 / 非中文字幕）
        """
        out: List[Tuple[str, bytes]] = []
        if content[:2] == b"PK":
            try:
                with zipfile.ZipFile(io.BytesIO(content)) as zf:
                    for info in zf.namelist():
                        if Path(info).suffix.lower() in SUB_EXTS and not info.startswith("__MACOSX"):
                            data = zf.read(info)
                            if self._valid_sub_content(data):
                                out.append((Path(info).name, data))
                            else:
                                logger.info(f"{self.plugin_name} 压缩包内文件未通过中文内容验证，跳过：{Path(info).name}")
            except Exception as err:
                logger.error(f"{self.plugin_name} 字幕压缩包解压失败[{sub_title}]：{err}")
            return out
        # 单文件直通：必须通过内容验证（罗斯案例：RAR 伪装成 .srt 落盘）
        name = sub_title or "subtitle"
        ext = Path(name).suffix.lower()
        if ext not in SUB_EXTS:
            ext = ".srt"
        if self._valid_sub_content(content):
            return [(f"subtitle{ext}", content)]
        logger.warning(
            f"{self.plugin_name} 下载内容未通过字幕验证（非文本或无中文），丢弃[{sub_title}]"
        )
        return []

    def _pick_best_file(self, files: List[Tuple[str, bytes]], season, ep, resolution) -> Optional[Tuple[str, bytes]]:
        best, best_score = None, -1
        for name, content in files:
            blob = name
            if not _has_cn_text(blob):
                continue
            score = 0
            if re.search(r"简|chs|gb|sc", blob, re.I):
                score += 5
            elif re.search(r"繁|cht|big5|tc", blob, re.I):
                score += 3
            if resolution:
                r = _detect_resolution(blob)
                if r == resolution:
                    score += 3
            if ep is not None:
                _, eps = _parse_season_episode(name)
                if eps and ep not in eps:
                    continue
                if eps and ep in eps:
                    score += 10
            if score > best_score:
                best, best_score = (name, content), score
        return best

    @staticmethod
    def _ffsubsync_quality_check(stdout_text: str, out_srt, video_dur: Optional[float]) -> Tuple[str, str]:
        """
        ffsubsync 产物质量自检（v1.2.0 改三态）：
        返回 (level, 说明)，level ∈ ("ok", "warn", "fail")
        - ok  ：offset/帧率因子在阈值内
        - warn：帧率因子偏离（字幕版本与视频存在差异，产物已按比例修正，建议人工核对）
        - fail：offset 极端 / 帧率因子极端 / 产物时间轴与视频时长明显不符
        """
        try:
            off = scale = None
            m = re.search(r"offset seconds:\s*(-?[\d.]+)", stdout_text or "")
            if m:
                off = float(m.group(1))
            m = re.search(r"framerate scale factor:\s*([\d.]+)", stdout_text or "")
            if m:
                scale = float(m.group(1))
            if off is not None and abs(off) > 60:
                return "fail", f"offset {off:.1f}s 超阈值(±60s)"
            if scale is not None and not (0.90 <= scale <= 1.15):
                return "fail", f"帧率因子 {scale:.3f} 超阈值(0.90~1.15)"
            if scale is not None and not (0.98 <= scale <= 1.02):
                return "warn", f"帧率因子 {scale:.3f}（字幕版本与视频存在差异，不建议采用）"
            if out_srt is not None:
                try:
                    txt = Path(out_srt).read_text(encoding="utf-8", errors="replace")
                except OSError:
                    txt = ""
                ts = [int(h) * 3600 + int(mn) * 60 + int(s) + int(ms) / 1000
                      for h, mn, s, ms in re.findall(r"(\d+):(\d+):(\d+),(\d+)\s*-->", txt)]
                if ts and video_dur:
                    last = max(ts)
                    if last > video_dur * 1.15 or last < video_dur * 0.4:
                        return "fail", f"产物末条 {last:.0f}s 与视频时长 {video_dur:.0f}s 明显不符"
            detail = []
            if off is not None:
                detail.append(f"offset {off:+.1f}s")
            if scale is not None:
                detail.append(f"帧率 {scale:.3f}")
            return "ok", "，".join(detail) if detail else "无质量数据"
        except Exception as err:
            return "ok", f"自检异常（放行）：{err}"

    @staticmethod
    def _video_duration(video_path: str) -> Optional[float]:
        """ffprobe 读视频时长（秒）；不可用返回 None。"""
        fp = shutil.which("ffprobe")
        if not fp:
            return None
        try:
            proc = subprocess.run([fp, "-v", "error", "-show_entries", "format=duration",
                                   "-of", "csv=p=0", str(video_path)],
                                  capture_output=True, timeout=60)
            return float(proc.stdout.decode("utf-8", "replace").strip() or 0) or None
        except Exception:
            return None

    @staticmethod
    def _subtitle_duration_ok(text: str, video_dur: float) -> Tuple[bool, Optional[float], str]:
        """解析字幕时间轴末条，与视频时长粗比对（拦不同影片/严重版本错配）。"""
        ts = [int(h) * 3600 + int(mn) * 60 + int(s) + int(ms) / 1000
              for h, mn, s, ms in re.findall(r"(\d+):(\d+):(\d+),(\d+)\s*-->", text or "")]
        if not ts:
            return True, None, "未解析到时间轴（放行，交由对齐自检）"
        last = max(ts)
        if last < video_dur * 0.7 or last > video_dur * 1.3:
            return False, last, f"字幕末条 {last:.0f}s 与视频时长 {video_dur:.0f}s 明显不符（疑似不同版本/影片）"
        return True, last, f"字幕末条 {last:.0f}s / 视频 {video_dur:.0f}s"

    def _align_subtitle(self, video_path: str, sub_src: Path, sub_dst: Path) -> bool:
        """
        ffsubsync 对齐；失败则直接用原字幕（复制）
        """
        self._ensure_ffs_env()
        ff = shutil.which("ffsubsync")
        try:
            if ff:
                cmd = [ff, video_path, "-i", str(sub_src), "-o", str(sub_dst)]
            else:
                cmd = ["python", "-m", "ffsubsync", video_path, "-i", str(sub_src), "-o", str(sub_dst)]
            logger.info(f"{self.plugin_name} 开始对齐时间轴：{sub_src.name}")
            proc = subprocess.run(cmd, capture_output=True, timeout=900)
            if proc.returncode == 0 and sub_dst.exists():
                level, qmsg = self._ffsubsync_quality_check(
                    (proc.stdout or b"").decode("utf-8", "replace"),
                    sub_dst, self._video_duration(str(video_path)))
                if level in ("fail", "warn"):
                    try:
                        sub_dst.unlink()
                    except OSError:
                        pass
                    logger.warning(f"{self.plugin_name} 对齐产物质量未达标（回滚用原字幕）：{sub_dst.name} | {qmsg}")
                    shutil.copyfile(sub_src, sub_dst)
                    return True
                logger.info(f"{self.plugin_name} 对齐完成：{sub_dst.name} | {qmsg}")
                try:
                    _done = self._fget("realign_done") or {}
                    _done[str(sub_dst)] = time.time()
                    self._fsave("realign_done", _done)
                except Exception:
                    pass
                return True
            logger.warning(f"{self.plugin_name} 对齐失败（ret={proc.returncode}），使用未对齐字幕")
        except Exception as err:
            logger.warning(f"{self.plugin_name} 对齐异常：{err}，使用未对齐字幕")
        try:
            shutil.copyfile(sub_src, sub_dst)
            return True
        except OSError:
            return False

    # ---------------- 落盘前规范化（防「写出去了但 Jellyfin 静默丢弃」） ----------------

    @staticmethod
    def _decode_sub_text(content: bytes) -> Tuple[str, str]:
        """
        解码字幕字节 → (文本, 实际编码)。按 utf-8-sig → utf-8 → gb18030 → big5 依次尝试。
        注意 utf-8-sig 放第一位：它能同时处理「带 BOM」和「不带 BOM」的 UTF-8，并把 BOM 去掉。
        全部失败返回 ("", "")。
        """
        for enc in ("utf-8-sig", "utf-8", "gb18030", "big5"):
            try:
                return content.decode(enc), enc
            except (UnicodeDecodeError, LookupError):
                continue
        return "", ""

    def _normalize_subtitle(self, content: bytes, file_name: str) -> Tuple[bytes, str]:
        """
        落盘前规范化，返回 (新内容, 说明)。规则：
          ① 编码统一成「无 BOM 的 UTF-8」—— 库里那批 GBK 老字幕 Jellyfin 的 ffprobe 探测会失败
          ② 首块完整性校验：
             - .ass/.ssa：必须以 [Script Info] 开头（文件头被截断过的会缺这一行）→ 无法修复即拒绝
             - .srt：首块必须是「序号 + 标准时间轴」；若开头是残缺块（如时间轴被截成 `7,360 -->`），
               丢弃这段残破前缀后再落盘
        返回内容为 b"" 表示不可用，调用方应放弃落盘、不要写进媒体库。
        """
        ext = Path(file_name or "").suffix.lower()
        text, enc = self._decode_sub_text(content)
        if not text or not text.strip():
            logger.warning(f"{self.plugin_name} 字幕编码无法识别或内容为空，放弃落盘：{file_name}")
            return b"", ""

        notes: List[str] = []
        if enc != "utf-8":
            notes.append(f"编码 {enc} → UTF-8")

        if ext in (".ass", ".ssa"):
            head = text.lstrip("\ufeff \t\r\n")
            if not head.startswith("[Script Info]"):
                logger.warning(
                    f"{self.plugin_name} ASS 字幕缺少 [Script Info] 头部（文件头疑似被截断），放弃落盘：{file_name}"
                )
                return b"", ""
            if text != head:
                notes.append("去掉头部空白/BOM")
                text = head
        else:
            # 标准 SRT 首块：序号行 + 两位小时的时间轴
            cue = re.compile(
                r"(?m)^[ \t]*(\d{1,6})[ \t]*\r?\n"
                r"[ \t]*(\d{2}:\d{2}:\d{2}[,.]\d{1,3})[ \t]*-->[ \t]*"
                r"(\d{2}:\d{2}:\d{2}[,.]\d{1,3})"
            )
            m = cue.search(text)
            if not m:
                logger.warning(
                    f"{self.plugin_name} SRT 首块时间轴不完整（文件头疑似被截断），放弃落盘：{file_name}"
                )
                return b"", ""
            if m.start() > 0:
                notes.append(f"丢弃残破前缀 {m.start()} 字节")
                text = text[m.start():]

        out = text.encode("utf-8")          # 无 BOM
        if out == content and not notes:
            return out, ""
        note = "；".join(notes) if notes else "规范化"
        logger.info(f"{self.plugin_name} 字幕已规范化（{note}）：{file_name}")
        return out, note

    def _save_subtitle(self, video_path: str, file_name: str, content: bytes, align: bool,
                       overwrite: bool = False) -> bool:
        """
        保存字幕到视频同目录：<视频名>.<标签>.<后缀>
        overwrite=True 时覆盖已存在的同名字幕（外部手动挂载用）；默认 False 保持原「已存在则跳过」行为。
        """
        video = Path(video_path)
        # 落盘前规范化：编码统一为无 BOM 的 UTF-8 + 首块完整性校验
        # （防「字幕写出去了，但 Jellyfin 的 ffprobe 探测失败 → 静默丢弃、用户看不到」）
        content, _norm_note = self._normalize_subtitle(content, file_name)
        if not content:
            return False
        # 正确性判定（v1.2.0 加）：字幕时间轴与视频时长粗比对，拦「不同影片/严重版本错配」
        _vdur = self._video_duration(str(video))
        if _vdur:
            _text, _ = self._decode_sub_text(content)
            _ok, _sdur, _smsg = self._subtitle_duration_ok(_text, _vdur)
            if not _ok:
                logger.warning(f"{self.plugin_name} 字幕正确性判定未通过，拒绝挂载：{file_name} | {_smsg}")
                self._notify_add("block", video.stem,
                                 f"⛔ {file_name} 正确性判定未通过已拒绝：{_smsg}")
                return False
        ext = Path(file_name).suffix.lower()
        final_path = video.parent / f"{video.stem}.{self._lang_tag}{ext}"
        if final_path.exists():
            if not overwrite:
                logger.info(f"{self.plugin_name} 字幕已存在，跳过：{final_path.name}")
                return True
            logger.info(f"{self.plugin_name} 字幕已存在，按覆盖选项替换：{final_path.name}")
        tmp_path = video.parent / f".{video.stem}.{self._lang_tag}.tmp{ext}"
        try:
            tmp_path.write_bytes(content)
        except OSError as err:
            logger.error(f"{self.plugin_name} 写入字幕失败：{final_path} - {err}")
            return False
        need_align = align and ext in ALIGNABLE_EXTS
        vp_l = video_path.lower()
        if Path(video_path).is_dir() or vp_l.endswith(".iso"):
            # 蓝光原盘（BDMV目录/ISO）：无音轨可抽，直接落盘不对齐
            logger.info(f"{self.plugin_name} 蓝光原盘/ISO，跳过对齐：{Path(video_path).name}")
            need_align = False
        if need_align:
            # 先落盘未对齐版（播放立即可用），对齐挂起后台异步完成后自动替换
            try:
                shutil.move(str(tmp_path), str(final_path))
                self._enqueue_align(str(video), str(final_path))
                self._notify_add("match", final_path.name, "✅ 已匹配（待后台对齐）")
                return True
            except OSError as err:
                logger.error(f"{self.plugin_name} 保存字幕失败：{err}")
                return False
        try:
            shutil.move(str(tmp_path), str(final_path))
            logger.info(f"{self.plugin_name} 字幕已保存：{final_path}")
            self._notify_add("match", final_path.name, "✅ 已匹配并落盘")
            return True
        except OSError as err:
            logger.error(f"{self.plugin_name} 保存字幕失败：{err}")
            return False

    # ---------------- 分组处理 ----------------

    def _process_movie(self, movie: dict) -> bool:
        # 双语关键词并行搜索，合并去重（标题校验防错片）
        orig = movie.get("original") or ""
        name = movie.get("name") or ""
        attempts = [h for h in dict.fromkeys([orig, name]) if h]
        resolution = _detect_resolution(movie["path"] or "")
        title_hints = attempts[:]
        logger.info(f"{self.plugin_name} [电影] {name} 开始匹配（关键词：{' / '.join(attempts)}）")
        all_subs: List[Any] = []
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=2) as ex:
            for r in ex.map(self._search_subtitles, attempts):
                all_subs.extend(r or [])
        if not all_subs:
            return False
        best = self._pick_best(all_subs, None, None, resolution, title_hints=title_hints)
        if not best:
            return False
        content = self._download_content(best)
        if not content:
            return False
        files = self._extract_sub_files(content, best.title or best.file_name or "")
        if not files:
            return False
        picked = self._pick_best_file(files, None, None, resolution) or files[0]
        return self._save_subtitle(movie["path"], picked[0], picked[1], self._align)

    @staticmethod
    def _extract_english_title(path: str) -> str:
        """
        从视频路径提取英文标题候选：文件名/目录名里的连续英文词段（≥2词）
        例：宿敌.The.Silent.Storm.S01.2024.2160p.WEB-DL... -> "The Silent Storm"
        """
        if not path:
            return ""
        stem = Path(path).name
        stem = re.sub(r"\.(mkv|mp4|ts|iso|avi|wmv|m2ts|mpg)$", "", stem, flags=re.I)
        parts = re.split(r"[.\-_()\[\]\s]+", stem)
        segs, cur = [], []
        for p in parts:
            if p and re.fullmatch(r"[A-Za-z][A-Za-z'&]*", p):
                cur.append(p)
            else:
                if cur:
                    segs.append(" ".join(cur))
                cur = []
        if cur:
            segs.append(" ".join(cur))
        bad = re.compile(
            r"^(WEB|DL|REMUX|HDR|DV|SDR|HEVC|H\.?26[45x]|X26[45x]|AVC|AAC|DDP?|DD\+?|FLAC|TrueHD|"
            r"ATMOS|10bit|8bit|BluRay|Blu|Ray|UHD|HFR|Vivid|Audios|DTS|MA|HD|PMTP|iT|COMPLETE|FULLSiZE|"
            r"iTA|ENG|GERMAN|NF|AMZN|ATVP|PCOK|DSNP|HMAX|MAX|QHstudIo|CMCTV|HDSWEB|HHWEB|AGSVWEB|"
            r"Taengoo|CHD|WiKi|EZTV)$", re.I)
        for seg in segs:
            words = seg.split()
            if len(words) >= 2 and not any(bad.match(w) for w in words):
                return seg
        return ""

    def _process_series(self, series: str, season: int, eps: List[dict]) -> bool:
        # 双语关键词并行搜索：中文名 + 路径提取英文名
        en = self._extract_english_title(eps[0].get("path") or "")
        attempts = [series] + ([en] if en and en.lower() != series.lower() else [])
        # 标题校验：中英任一命中（最终字幕只要是中文即可）
        title_hints = [series] + ([en] if en else [])
        logger.info(f"{self.plugin_name} [剧集] {series} 第{season}季 {len(eps)}集缺失，开始匹配（关键词：{' / '.join(attempts)}）")
        all_subs: List[Any] = []
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=2) as ex:
            for r in ex.map(self._search_subtitles, attempts):
                all_subs.extend(r or [])
        if not all_subs:
            return False
        saved_eps = set()
        # 整季批量：按下载包去重，避免同一包重复下载
        for sub in all_subs:
            if len(saved_eps) >= len(eps):
                break
            if not self._is_chinese_sub(sub):
                continue
            blob = f"{sub.title or ''} {sub.description or ''} {sub.file_name or ''}"
            sub_season = _parse_season_episode(blob)[0]
            meta = getattr(sub, "meta_info", None)
            if sub_season is None and meta is not None:
                ms = getattr(meta, "season", None)
                if ms is not None:
                    sub_season = int(ms)
            if sub_season is not None and sub_season != season:
                continue
            if sub_season is None and season > 1:
                continue
            content = self._download_content(sub)
            if not content:
                continue
            files = self._extract_sub_files(content, sub.title or sub.file_name or "")
            for it in eps:
                if it["id"] in saved_eps:
                    continue
                ep_no = it.get("episode")
                resolution = _detect_resolution(it["path"] or "")
                picked = self._pick_best_file(files, season, ep_no, resolution)
                if not picked and len(files) == 1 and len(eps) == 1:
                    picked = files[0]
                if not picked:
                    continue
                if self._save_subtitle(it["path"], picked[0], picked[1], self._align):
                    saved_eps.add(it["id"])
        return len(saved_eps) > 0
