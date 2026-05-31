#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
硬件代码缺陷检测、定位与修复系统性文献综述检索脚本

功能：
1. 按系统性文献综述协议进行多主题检索
2. Semantic Scholar paper search + offset 分页
3. 可选 arXiv API 补充最新预印本文献，默认关闭
4. 自动执行标题/摘要层面的纳入与排除初筛
5. 默认排除纯软件代码、制造/图像/材料缺陷、纯 PPA/物理设计/后端优化类论文
6. 自动分类：硬件代码缺陷检测、缺陷定位、自动修复、调试反馈、
   Lint/静态分析、安全缺陷、Benchmark/Dataset、LLM/Agent 方法、综述等
7. 输出 Markdown 报告 + JSON 原始结构化结果 + 检索式记录

依赖：
    pip install requests

建议环境变量：
    export SEMANTIC_SCHOLAR_API_KEY="你的S2 API KEY"
    export BYPASS_PROXY=0                 # 可选：设为 0 时允许 requests 读取系统代理
    export ENABLE_ARXIV=1                 # 可选：设为 1 时启用 arXiv 补充预印本
    export YEAR_FROM=2020
    export OUTPUT_DIR="/home/zk/桌面/文献/codex文献检索/检索报告"
"""

import os
import re
import json
import time
import html
import hashlib
import datetime
import xml.etree.ElementTree as ET
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import requests


# =========================================================
# 基础配置
# =========================================================

YEAR_FROM = int(os.getenv("YEAR_FROM", "2020"))

S2_API_KEY = os.getenv(
    "SEMANTIC_SCHOLAR_API_KEY",
    "s2k-OoBn7hq3HJBOZhkX42AROvX2ICQC6qq5NEYyU4g0",
).strip()
BYPASS_PROXY = os.getenv("BYPASS_PROXY", "1") == "1"

# Semantic Scholar paper search 没有必要无限翻页，定时任务建议先限制
S2_MAX_PAGES_PER_QUERY = int(os.getenv("S2_MAX_PAGES_PER_QUERY", "3"))
S2_LIMIT_PER_PAGE = int(os.getenv("S2_LIMIT_PER_PAGE", "100"))
S2_SLEEP_SECONDS = float(os.getenv("S2_SLEEP_SECONDS", "2.0"))
REQUEST_CONNECT_TIMEOUT = float(os.getenv("REQUEST_CONNECT_TIMEOUT", "10"))
REQUEST_READ_TIMEOUT = float(os.getenv("REQUEST_READ_TIMEOUT", "20"))
REQUEST_TIMEOUT = (REQUEST_CONNECT_TIMEOUT, REQUEST_READ_TIMEOUT)

# arXiv API 不需要 key；默认关闭，避免触发 arXiv 限流
ENABLE_ARXIV = os.getenv("ENABLE_ARXIV", "0") == "1"
ARXIV_MAX_RESULTS_PER_QUERY = int(os.getenv("ARXIV_MAX_RESULTS_PER_QUERY", "50"))
ARXIV_SLEEP_SECONDS = float(os.getenv("ARXIV_SLEEP_SECONDS", "3.2"))
ARXIV_DISABLE_AFTER_ERRORS = int(os.getenv("ARXIV_DISABLE_AFTER_ERRORS", "5"))
ARXIV_LAST_ERROR = False

RUN_TIME = datetime.datetime.now()
NOW_STR = RUN_TIME.strftime("%Y-%m-%d %H:%M:%S")
FILE_TIME_STR = RUN_TIME.strftime("%Y%m%d_%H%M%S")

SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_OUTPUT_DIR = SCRIPT_DIR / "检索报告"
OUTPUT_DIR = Path(os.getenv("OUTPUT_DIR", str(DEFAULT_OUTPUT_DIR))).expanduser()
REPORT_STEM = f"S2_hardware_code_defects+{FILE_TIME_STR}"
REPORT_MD = OUTPUT_DIR / f"{REPORT_STEM}.md"
REPORT_JSON = OUTPUT_DIR / f"{REPORT_STEM}.json"


# =========================================================
# 系统性文献综述协议与检索矩阵
# 默认范围：硬件代码（RTL/HDL/Verilog/SystemVerilog/VHDL 等）的
# 缺陷检测、缺陷定位与自动修复/调试方向。
# 检索词设置思路：
# 1. 硬件代码语境词：RTL/HDL/Verilog/SystemVerilog/VHDL/Chisel/FIRRTL/HLS 等
# 2. 缺陷任务词：bug/defect/fault/error/vulnerability + detection/localization/repair
# 3. 方法词：LLM/agent/ML/static analysis/formal/program analysis 等作为召回和加权维度
# 4. 噪声排除：软件代码、制造/图像/材料缺陷、纯后端物理设计/PPA
# =========================================================

REVIEW_QUESTION = (
    "What methods, datasets, benchmarks, and evaluation practices have been "
    "reported for hardware-code defect detection, bug/fault localization, and "
    "automatic repair/debugging in RTL/HDL/Verilog/SystemVerilog/VHDL designs?"
)

INCLUSION_CRITERIA = [
    "Title or abstract explicitly concerns hardware code or digital hardware design code "
    "(e.g., RTL, HDL, Verilog, SystemVerilog, VHDL, Chisel, FIRRTL, HLS, hardware description language).",
    "Title or abstract explicitly concerns defect/bug/fault/error/vulnerability detection, "
    "localization/root-cause analysis, repair/fixing/patching, debugging, lint, or static analysis.",
    "LLM/agent/ML/static-analysis/formal-method/program-analysis papers are included when "
    "their task is hardware-code defect detection, localization, or repair.",
    "Benchmark, dataset, and survey papers are included only when they address hardware-code defects.",
    f"Publication year is {YEAR_FROM} or later when a year is available.",
]

EXCLUSION_CRITERIA = [
    "Pure software-code defect detection/localization/repair without a hardware-code context.",
    "Manufacturing, wafer, surface, visual, material, structural, or chip-defect inspection papers.",
    "Medical, psychological, biomedical, analog/RF/device-only, or unrelated AI work.",
    "Pure physical-design/PPA/place-route/timing-closure/ECO optimization papers.",
    "Hardware-code generation, synthesis optimization, verification, or benchmark papers that do "
    "not explicitly address defects, bugs, faults, errors, vulnerabilities, debugging, localization, or repair.",
]

QUERY_MATRIX: Dict[str, List[str]] = {
    "general_hardware_code_defects": [
        "hardware code defect detection",
        "hardware code bug detection",
        "hardware code fault detection",
        "hardware code vulnerability detection",
        "hardware design bug detection",
        "hardware design defect detection",
        "hardware description language bug detection",
        "hardware description language defect detection",
        "digital hardware design bug detection",
        "digital hardware design defect detection",
    ],

    "defect_detection": [
        "RTL bug detection",
        "RTL defect detection",
        "RTL fault detection",
        "RTL error detection",
        "RTL vulnerability detection",
        "Verilog bug detection",
        "Verilog defect detection",
        "Verilog vulnerability detection",
        "SystemVerilog bug detection",
        "VHDL bug detection",
        "HDL bug detection",
        "HDL defect detection",
    ],

    "static_analysis_lint": [
        "RTL lint defect detection",
        "RTL lint bug detection",
        "Verilog lint bug detection",
        "SystemVerilog lint bug detection",
        "HDL static analysis bug detection",
        "RTL static analysis defect detection",
        "Verilog static analysis defect detection",
        "hardware description language static analysis",
        "Verilog semantic bug detection",
        "RTL rule violation detection",
    ],

    "bug_localization": [
        "RTL bug localization",
        "RTL fault localization",
        "RTL error localization",
        "RTL root cause analysis",
        "Verilog bug localization",
        "Verilog fault localization",
        "Verilog error localization",
        "HDL bug localization",
        "hardware code bug localization",
        "hardware code fault localization",
        "hardware design bug localization",
        "hardware description language fault localization",
    ],

    "repair_debugging": [
        "RTL repair",
        "RTL bug repair",
        "RTL defect repair",
        "RTL debugging",
        "Verilog repair",
        "Verilog bug repair",
        "Verilog bug fixing",
        "Verilog debugging",
        "HDL repair",
        "HDL bug repair",
        "hardware code repair",
        "hardware code bug fixing",
        "hardware design repair",
        "automated repair RTL",
        "automated repair Verilog",
        "program repair Verilog",
    ],

    "feedback_based_repair": [
        "compiler feedback RTL repair",
        "compiler feedback Verilog repair",
        "compilation error Verilog repair",
        "synthesis error RTL repair",
        "synthesis error Verilog repair",
        "simulation feedback RTL repair",
        "simulation feedback Verilog repair",
        "test feedback Verilog repair",
        "counterexample guided RTL repair",
        "counterexample guided Verilog repair",
    ],

    "llm_agent_defect_workflows": [
        "large language model RTL bug detection",
        "large language model Verilog bug detection",
        "large language model HDL static analysis",
        "LLM RTL bug localization",
        "LLM Verilog bug localization",
        "LLM RTL repair",
        "LLM Verilog repair",
        "LLM RTL debugging",
        "LLM Verilog debugging",
        "agent RTL debugging",
        "agent Verilog repair",
        "self debugging Verilog large language model",
        "self correcting Verilog large language model",
        "tool augmented LLM Verilog repair",
    ],

    "benchmark_dataset": [
        "RTL bug benchmark",
        "RTL defect dataset",
        "RTL repair benchmark",
        "RTL debugging benchmark",
        "Verilog bug benchmark",
        "Verilog defect dataset",
        "Verilog repair benchmark",
        "Verilog debugging benchmark",
        "HDL defect dataset",
        "HDL repair benchmark",
        "hardware code bug benchmark",
        "hardware code defect dataset",
        "hardware code repair benchmark",
    ],

    "security_vulnerability": [
        "RTL vulnerability detection",
        "Verilog vulnerability detection",
        "SystemVerilog vulnerability detection",
        "HDL vulnerability detection",
        "hardware code vulnerability detection",
        "hardware design vulnerability detection",
        "hardware Trojan detection RTL",
        "hardware Trojan detection Verilog",
        "CWE detection Verilog",
        "security bug detection RTL",
    ],

    "survey_position": [
        "survey RTL bug detection",
        "survey RTL repair",
        "survey Verilog bug detection",
        "survey Verilog repair",
        "survey hardware code defect detection",
        "survey hardware code repair",
        "review hardware code bug detection",
        "review hardware code defect repair",
        "survey LLM RTL debugging",
        "survey LLM Verilog repair",
    ],
}


# =========================================================
# 正负向过滤词
# =========================================================

STRONG_HARDWARE_CODE_TERMS = [
    "rtl",
    "register-transfer",
    "register transfer",
    "register transfer level",
    "verilog",
    "systemverilog",
    "vhdl",
    "hdl",
    "chisel",
    "firrtl",
    "bluespec",
    "bsv",
    "hls",
    "high-level synthesis",
    "hardware description",
    "hardware description language",
    "hardware code",
    "hardware source code",
    "design code",
    "rtl code",
    "hdl code",
    "verilog code",
    "systemverilog code",
    "vhdl code",
]

HARDWARE_CODE_CONTEXT_TERMS = STRONG_HARDWARE_CODE_TERMS + [
    "eda",
    "electronic design automation",
    "hardware design automation",
    "hardware design",
    "digital hardware design",
    "digital design",
    "logic design",
    "chip design",
    "fpga design",
    "asic design",
    "synthesis error",
    "simulation error",
    "compilation error",
]

DEFECT_TASK_TERMS = [
    "bug",
    "bugs",
    "defect",
    "defects",
    "fault",
    "faults",
    "error",
    "errors",
    "vulnerability",
    "vulnerabilities",
    "bug detection",
    "defect detection",
    "fault detection",
    "error detection",
    "vulnerability detection",
    "bug localization",
    "fault localization",
    "error localization",
    "defect localization",
    "root cause",
    "root-cause",
    "root cause analysis",
    "debug",
    "debugging",
    "repair",
    "repairs",
    "bug repair",
    "defect repair",
    "automated repair",
    "automatic repair",
    "program repair",
    "bug fixing",
    "fixing",
    "patch",
    "patch generation",
    "self-debugging",
    "self debugging",
    "self-correcting",
    "self correcting",
    "lint",
    "coding rule",
    "rule checking",
    "rule violation",
    "static analysis",
    "semantic analysis",
    "counterexample guided",
    "compiler feedback",
    "compilation error",
    "synthesis error",
    "simulation feedback",
    "test feedback",
]

METHOD_TERMS = [
    "llm",
    "large language model",
    "language model",
    "generative ai",
    "generative artificial intelligence",
    "chatgpt",
    "gpt",
    "agent",
    "agents",
    "agentic",
    "multi-agent",
    "copilot",
    "autonomous",
    "tool-in-the-loop",
    "feedback loop",
    "machine learning",
    "deep learning",
    "neural network",
    "transformer",
    "foundation model",
    "foundation models",
    "reinforcement learning",
    "lint",
    "static analysis",
    "program analysis",
    "formal method",
    "formal methods",
    "formal verification",
    "symbolic execution",
    "model checking",
    "constant propagation",
    "dataflow analysis",
    "control flow",
    "abstract interpretation",
    "constraint solving",
    "satisfiability",
    "sat",
    "smt",
    "planner",
    "verifier",
    "critic",
]

NEGATIVE_NOISE_TERMS = [
    # 非电子设计自动化语义的 EDA
    "exploratory data analysis",
    "electrodermal activity",
    "eating disorder",
    "emergency department",
    "education data analysis",

    # 医学/生物/心理学强噪声
    "clinical",
    "patient",
    "disease",
    "cancer",
    "neural disease",
    "biomedical",
    "psychological",
    "emotion recognition",
    "skin conductance",

    # 制造/图像/材料/工业外观缺陷，不属于硬件代码缺陷
    "surface defect",
    "visual defect",
    "image defect",
    "industrial defect",
    "fabric defect",
    "wafer defect",
    "chip defect inspection",
    "semiconductor defect inspection",
    "defect inspection",
    "defect segmentation",
    "defect classification",
    "crack detection",
    "scratch detection",
    "steel defect",
    "textile defect",
    "crystal defect",
    "material defect",
    "product defect",

    # 纯软件工程方向；若标题/摘要同时出现 RTL/Verilog/HDL 等强硬件代码词，仍可纳入
    "software defect prediction",
    "software bug localization",
    "software bug detection",
    "software fault localization",
    "software vulnerability detection",
    "java bug",
    "python bug",
    "javascript bug",
    "android bug",

    # 模拟/器件方向，默认不是本任务重点
    "analog",
    "mixed-signal",
    "mixed signal",
    "op-amp",
    "operational amplifier",
    "adc",
    "dac",
    "rf circuit",
    "cmos image sensor",
    "memristor",
    "photonic",
    "quantum device",
]

# 后端/PPA/物理设计方向：用于过滤“纯后端”论文
PHYSICAL_DESIGN_TERMS = [
    "ppa closure",
    "ppa optimization",
    "performance power area",
    "performance-power-area",
    "physical design",
    "floorplan",
    "floorplanning",
    "placement",
    "placer",
    "global placement",
    "detailed placement",
    "routing",
    "router",
    "global routing",
    "detailed routing",
    "timing closure",
    "clock tree synthesis",
    "cts",
    "eco optimization",
    "engineering change order",
    "layout",
    "place and route",
    "place-and-route",
    "post-layout",
    "post route",
    "post-route",
    "congestion optimization",
]

CATEGORY_KEYWORDS: Dict[str, List[str]] = {
    "硬件代码缺陷检测": [
        "bug detection", "defect detection", "fault detection", "error detection",
        "bug prediction", "defect prediction", "vulnerability detection",
        "hardware trojan detection", "security bug detection"
    ],
    "硬件代码缺陷定位": [
        "bug localization", "fault localization", "error localization",
        "defect localization", "root cause", "root-cause", "root cause analysis"
    ],
    "硬件代码自动修复": [
        "rtl repair", "verilog repair", "hdl repair", "bug repair",
        "defect repair", "automated repair", "automatic repair", "program repair",
        "bug fixing", "patch generation", "code repair"
    ],
    "硬件代码调试/反馈闭环": [
        "debugging", "self-debugging", "self debugging", "self-correcting",
        "compiler feedback", "compilation error", "synthesis error",
        "simulation feedback", "test feedback", "counterexample guided"
    ],
    "静态分析/Lint/规则检查": [
        "lint", "static analysis", "bug detection", "defect detection",
        "vulnerability", "simulation log", "synthesis log",
        "coding rule", "rule checking", "rule violation", "root cause",
        "semantic analysis", "program analysis", "constant propagation"
    ],
    "安全缺陷/漏洞检测": [
        "vulnerability", "cwe", "security bug", "hardware trojan",
        "information flow", "side channel", "secure rtl"
    ],
    "LLM/Agent方法": [
        "llm", "large language model", "generative ai", "chatgpt",
        "gpt", "agent", "multi-agent", "copilot", "tool augmented"
    ],
    "Benchmark/Dataset": [
        "benchmark", "dataset", "bug benchmark", "defect dataset",
        "repair benchmark", "debugging benchmark", "verilogeval",
        "rtllm", "openllm-rtl", "asserteval", "hdlbits"
    ],
    "综述/立场论文": [
        "survey", "review", "systematic literature review", "position paper"
    ],
}


NAMED_BENCHMARK_TERMS = [
    "verilogeval",
    "rtllm",
    "openllm-rtl",
    "asserteval",
    "hdlbits",
    "bug benchmark",
    "defect dataset",
    "repair benchmark",
]

TITLE_BOOST_TERMS = NAMED_BENCHMARK_TERMS + [
    "eda",
    "rtl",
    "verilog",
    "systemverilog",
    "vhdl",
    "hdl",
    "lint",
    "bug",
    "defect",
    "fault",
    "error",
    "repair",
    "debugging",
    "localization",
    "vulnerability",
]

SURVEY_TERMS = [
    "survey",
    "review",
    "systematic literature review",
    "position paper",
]

LLM_TERMS = [
    "llm",
    "large language model",
    "generative ai",
]

HARDWARE_CODE_SURVEY_CONTEXT_TERMS = STRONG_HARDWARE_CODE_TERMS + [
    "hardware code defect",
    "hardware design bug",
    "hardware design defect",
    "digital design bug",
]


# =========================================================
# 工具函数
# =========================================================

def log(msg: str) -> None:
    print(f"[{datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {msg}", flush=True)


def make_session() -> requests.Session:
    session = requests.Session()
    if BYPASS_PROXY:
        session.trust_env = False
    return session


def normalize_text(s: Optional[str]) -> str:
    if not s:
        return ""
    s = html.unescape(str(s))
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def normalize_title(title: str) -> str:
    title = normalize_text(title).lower()
    title = re.sub(r"[^a-z0-9\u4e00-\u9fff]+", " ", title)
    title = re.sub(r"\s+", " ", title).strip()
    return title


def normalize_arxiv_id(arxiv_id: str) -> str:
    arxiv_id = normalize_text(arxiv_id).lower()
    arxiv_id = arxiv_id.rstrip("/")
    arxiv_id = arxiv_id.split("/")[-1]
    arxiv_id = re.sub(r"v\d+$", "", arxiv_id)
    return arxiv_id


def stable_hash(text: str) -> str:
    return hashlib.sha1(text.encode("utf-8", errors="ignore")).hexdigest()[:16]


def safe_year(value: Any) -> int:
    if value is None:
        return 0
    try:
        return int(str(value)[:4])
    except (TypeError, ValueError):
        return 0


def extract_year_from_date(date_str: Optional[str]) -> int:
    if not date_str:
        return 0
    m = re.match(r"(\d{4})", date_str)
    return int(m.group(1)) if m else 0


@lru_cache(maxsize=1024)
def term_pattern(term: str) -> re.Pattern:
    term = normalize_text(term).lower()
    if not term:
        return re.compile(r"(?!)")

    parts = [re.escape(part) for part in re.split(r"\s+", term) if part]
    pattern = r"\s+".join(parts)

    if term[0].isalnum():
        pattern = rf"(?<![a-z0-9]){pattern}"
    if term[-1].isalnum():
        pattern = rf"{pattern}(?![a-z0-9])"

    return re.compile(pattern, re.IGNORECASE)


def contains_any(text: str, terms: Sequence[str]) -> bool:
    t = normalize_text(text).lower()
    return any(term_pattern(term).search(t) for term in terms)


def count_hits(text: str, terms: Sequence[str]) -> int:
    t = normalize_text(text).lower()
    return sum(1 for term in terms if term_pattern(term).search(t))


def quote_phrase_for_s2(term: str) -> str:
    # S2 ranks natural-language keyword strings well; quoting the whole query
    # makes the search too exact for systematic-review recall.
    return normalize_text(term).replace('"', "")


def build_arxiv_query(term: str) -> str:
    """
    arXiv 查询语法：
    - 使用 all:token 查标题、摘要等字段
    - 多词检索式拆成 token AND token，避免完整短语匹配造成漏检
    - 不强行加 submittedDate 范围，避免日期语法兼容问题
    - 通过 sortBy=submittedDate desc 获取最新结果，再在本地按 year >= YEAR_FROM 过滤
    - 强制叠加硬件代码语境和缺陷任务语境，避免召回普通软件或制造缺陷论文
    """
    tokens = [
        tok
        for tok in re.split(r"[^A-Za-z0-9\-]+", term.replace('"', ""))
        if tok
    ]
    base = " AND ".join(f"all:{tok}" for tok in tokens) if tokens else "all:RTL"

    hardware_context = (
        '(all:Verilog OR all:SystemVerilog OR all:RTL OR all:HDL OR '
        'all:VHDL OR all:Chisel OR all:FIRRTL OR all:HLS OR '
        'all:"hardware code" OR all:"hardware description" OR '
        'all:"hardware description language" OR all:"hardware design" OR '
        'all:"digital design" OR all:"electronic design automation")'
    )
    defect_context = (
        '(all:bug OR all:defect OR all:fault OR all:error OR '
        'all:vulnerability OR all:debugging OR all:repair OR all:fixing OR '
        'all:localization OR all:lint OR all:"static analysis")'
    )
    return f"{base} AND {hardware_context} AND {defect_context}"


def is_backend_physical_only(title: str, abstract: str) -> bool:
    """
    过滤纯 PPA / 物理设计 / 后端优化论文。
    注意：
    - 如果论文同时明显属于 RTL/Verilog/HDL 等硬件代码缺陷任务，则不排除。
    - 如果是硬件代码缺陷综述，也不强行排除。
    """
    text = f"{title} {abstract}".lower()

    has_backend = contains_any(text, PHYSICAL_DESIGN_TERMS)
    if not has_backend:
        return False

    has_strong_hardware_code = contains_any(text, STRONG_HARDWARE_CODE_TERMS)
    has_defect_task = contains_any(text, DEFECT_TASK_TERMS)
    has_survey = contains_any(text, SURVEY_TERMS)
    has_hardware_code_survey = (
        has_survey
        and contains_any(text, HARDWARE_CODE_SURVEY_CONTEXT_TERMS)
        and has_defect_task
    )

    if has_strong_hardware_code and has_defect_task:
        return False
    if has_hardware_code_survey:
        return False

    return True


def classify_paper(title: str, abstract: str, query_categories: List[str]) -> List[str]:
    text = f"{title} {abstract}".lower()
    labels = []

    for label, kws in CATEGORY_KEYWORDS.items():
        if contains_any(text, kws):
            labels.append(label)

    fallback_map = {
        "general_hardware_code_defects": "硬件代码缺陷检测",
        "defect_detection": "硬件代码缺陷检测",
        "static_analysis_lint": "静态分析/Lint/规则检查",
        "bug_localization": "硬件代码缺陷定位",
        "repair_debugging": "硬件代码自动修复",
        "feedback_based_repair": "硬件代码调试/反馈闭环",
        "llm_agent_defect_workflows": "LLM/Agent方法",
        "benchmark_dataset": "Benchmark/Dataset",
        "security_vulnerability": "安全缺陷/漏洞检测",
        "survey_position": "综述/立场论文",
    }

    for cat in query_categories:
        if cat in fallback_map and fallback_map[cat] not in labels:
            labels.append(fallback_map[cat])

    if not labels:
        labels.append("待人工复核")

    return labels


def compute_relevance_score(
    title: str,
    abstract: str,
    query_categories: List[str],
) -> Tuple[int, List[str]]:
    """
    简单规则评分：
    - 硬件代码词越多越高
    - 缺陷检测/定位/修复任务词越多越高
    - LLM/Agent/ML/静态分析/形式化等方法词作为加分项
    - 标题命中权重大于摘要
    - 明显噪声扣分
    - 纯后端/PPA/物理设计论文扣分
    """
    title_l = title.lower()
    abstract_l = abstract.lower()
    text_l = f"{title_l} {abstract_l}"

    reasons = []
    score = 0

    title_hardware_hits = count_hits(title_l, HARDWARE_CODE_CONTEXT_TERMS)
    abstract_hardware_hits = count_hits(abstract_l, HARDWARE_CODE_CONTEXT_TERMS)
    title_task_hits = count_hits(title_l, DEFECT_TASK_TERMS)
    abstract_task_hits = count_hits(abstract_l, DEFECT_TASK_TERMS)
    title_method_hits = count_hits(title_l, METHOD_TERMS)
    abstract_method_hits = count_hits(abstract_l, METHOD_TERMS)
    negative_hits = count_hits(text_l, NEGATIVE_NOISE_TERMS)
    backend_hits = count_hits(text_l, PHYSICAL_DESIGN_TERMS)

    score += title_hardware_hits * 6
    score += abstract_hardware_hits * 2
    score += title_task_hits * 7
    score += abstract_task_hits * 3
    score += title_method_hits * 3
    score += abstract_method_hits * 1

    if query_categories:
        score += min(len(set(query_categories)), 3) * 2

    if title_hardware_hits:
        reasons.append(f"标题命中硬件代码语境词 {title_hardware_hits} 个")
    if abstract_hardware_hits:
        reasons.append(f"摘要命中硬件代码语境词 {abstract_hardware_hits} 个")
    if title_task_hits:
        reasons.append(f"标题命中缺陷检测/定位/修复任务词 {title_task_hits} 个")
    if abstract_task_hits:
        reasons.append(f"摘要命中缺陷检测/定位/修复任务词 {abstract_task_hits} 个")
    if title_method_hits:
        reasons.append(f"标题命中方法词 {title_method_hits} 个")
    if abstract_method_hits:
        reasons.append(f"摘要命中方法词 {abstract_method_hits} 个")

    if negative_hits:
        score -= negative_hits * 6
        reasons.append(f"存在潜在噪声词 {negative_hits} 个")

    if backend_hits:
        reasons.append(
            f"命中后端/PPA/物理设计词 {backend_hits} 个，若为纯后端将被过滤"
        )

    boost_hits = count_hits(title_l, TITLE_BOOST_TERMS)
    if boost_hits:
        score += boost_hits * 4
        reasons.append(f"标题命中硬件代码缺陷主题强化词 {boost_hits} 个")

    return score, reasons


def screen_paper(title: str, abstract: str, score: int) -> Tuple[bool, List[str]]:
    """
    系统性综述的标题/摘要自动初筛。
    年份过滤在外层做；这里执行主题纳入/排除标准。
    """
    text_l = f"{title} {abstract}".lower()
    reasons = []

    if is_backend_physical_only(title, abstract):
        return False, ["排除：纯后端/PPA/物理设计方向"]

    has_hardware_context = contains_any(text_l, HARDWARE_CODE_CONTEXT_TERMS)
    has_strong_hardware_code = contains_any(text_l, STRONG_HARDWARE_CODE_TERMS)
    has_defect_task = contains_any(text_l, DEFECT_TASK_TERMS)
    has_method = contains_any(text_l, METHOD_TERMS)
    has_named = contains_any(text_l, NAMED_BENCHMARK_TERMS)
    has_noise = contains_any(text_l, NEGATIVE_NOISE_TERMS)

    if not has_hardware_context:
        return False, ["排除：标题/摘要未命中 RTL/HDL/Verilog 等硬件代码语境"]

    if not has_defect_task:
        return False, ["排除：标题/摘要未命中缺陷检测、定位、调试或修复任务语境"]

    reasons.append("纳入：同时命中硬件代码语境与缺陷检测/定位/修复任务语境")

    if has_method:
        reasons.append("加权：命中 LLM/Agent/ML/静态分析/形式化等方法语境")
    if has_named:
        reasons.append("加权：命中硬件代码相关 benchmark/dataset 语境")

    if has_noise and not has_strong_hardware_code and score < 18:
        return False, ["排除：潜在噪声领域命中，且未命中强硬件代码词"]

    if score < 10:
        return False, ["排除：相关性评分低于自动初筛阈值"]

    return True, reasons


def is_relevant_paper(title: str, abstract: str, score: int) -> bool:
    included, _ = screen_paper(title, abstract, score)
    return included


def paper_sort_key(p: Dict[str, Any]) -> Tuple[int, str, int, int]:
    year = safe_year(p.get("year"))
    pub_date = p.get("publicationDate") or ""
    score = int(p.get("relevanceScore", 0))
    citations = int(p.get("citationCount") or 0)
    return year, pub_date, score, citations


# =========================================================
# Semantic Scholar 检索
# =========================================================

def s2_search(query: str) -> List[Dict[str, Any]]:
    """
    使用 Semantic Scholar Graph API paper search。
    普通 search 使用 limit/offset 分页，响应体比 bulk search 更可控。
    """
    endpoint = "https://api.semanticscholar.org/graph/v1/paper/search"

    fields = ",".join([
        "paperId",
        "title",
        "url",
        "year",
        "publicationDate",
        "citationCount",
        "abstract",
        "openAccessPdf",
        "externalIds",
        "authors",
        "venue",
        "publicationVenue",
        "fieldsOfStudy",
        "publicationTypes",
    ])

    headers = {}
    if S2_API_KEY:
        headers["x-api-key"] = S2_API_KEY

    session = make_session()
    all_items: List[Dict[str, Any]] = []
    offset = 0

    for page_idx in range(S2_MAX_PAGES_PER_QUERY):
        params = {
            "query": query,
            "fields": fields,
            "year": f"{YEAR_FROM}-",
            "limit": S2_LIMIT_PER_PAGE,
            "offset": offset,
        }

        time.sleep(S2_SLEEP_SECONDS)

        try:
            resp = session.get(
                endpoint,
                params=params,
                headers=headers,
                timeout=REQUEST_TIMEOUT,
            )
        except requests.exceptions.RequestException as e:
            log(f"S2 网络异常: query={query}, err={e}")
            break

        if resp.status_code == 429:
            wait = 8 + page_idx * 5
            log(f"S2 限速 429，等待 {wait}s 后重试: {query}")
            time.sleep(wait)
            try:
                resp = session.get(
                    endpoint,
                    params=params,
                    headers=headers,
                    timeout=REQUEST_TIMEOUT,
                )
            except requests.exceptions.RequestException as e:
                log(f"S2 重试失败: query={query}, err={e}")
                break

        if resp.status_code != 200:
            log(
                f"S2 响应异常: status={resp.status_code}, "
                f"query={query}, body={resp.text[:200]}"
            )
            break

        try:
            data = resp.json()
        except ValueError as e:
            log(f"S2 JSON 解析失败: query={query}, err={e}")
            break

        batch = data.get("data", []) or []
        all_items.extend(batch)

        next_offset = data.get("next")
        if next_offset is None or not batch:
            break
        offset = int(next_offset)

    return all_items


def normalize_s2_paper(raw: Dict[str, Any], category: str, query: str) -> Optional[Dict[str, Any]]:
    title = normalize_text(raw.get("title"))
    if not title:
        return None

    abstract = normalize_text(raw.get("abstract"))
    year = safe_year(raw.get("year")) or extract_year_from_date(raw.get("publicationDate"))

    if year and year < YEAR_FROM:
        return None

    authors = []
    for a in raw.get("authors") or []:
        name = normalize_text(a.get("name"))
        if name:
            authors.append(name)

    external_ids = raw.get("externalIds") or {}
    doi = external_ids.get("DOI")
    arxiv_id = normalize_arxiv_id(external_ids.get("ArXiv") or "")

    pdf_url = ""
    pdf_obj = raw.get("openAccessPdf") or {}
    if isinstance(pdf_obj, dict):
        pdf_url = pdf_obj.get("url") or ""

    score, reasons = compute_relevance_score(title, abstract, [category])
    included, screening_reasons = screen_paper(title, abstract, score)
    if not included:
        return None

    paper = {
        "source": ["Semantic Scholar"],
        "paperId": raw.get("paperId"),
        "title": title,
        "authors": authors,
        "year": year,
        "publicationDate": raw.get("publicationDate") or "",
        "venue": normalize_text(raw.get("venue")),
        "publicationVenue": raw.get("publicationVenue"),
        "publicationTypes": raw.get("publicationTypes") or [],
        "fieldsOfStudy": raw.get("fieldsOfStudy") or [],
        "url": raw.get("url") or "",
        "pdfUrl": pdf_url,
        "doi": doi or "",
        "arxivId": arxiv_id,
        "citationCount": raw.get("citationCount") or 0,
        "abstract": abstract,
        "queryCategories": [category],
        "queries": [query],
        "labels": classify_paper(title, abstract, [category]),
        "relevanceScore": score,
        "relevanceReasons": reasons + screening_reasons,
        "screeningDecision": "included",
        "screeningReasons": screening_reasons,
    }
    return paper


# =========================================================
# arXiv 检索，可选，默认关闭
# =========================================================

def arxiv_search(query: str) -> List[Dict[str, Any]]:
    global ARXIV_LAST_ERROR
    ARXIV_LAST_ERROR = False

    endpoint = "https://export.arxiv.org/api/query"

    params = {
        "search_query": query,
        "start": 0,
        "max_results": ARXIV_MAX_RESULTS_PER_QUERY,
        "sortBy": "submittedDate",
        "sortOrder": "descending",
    }

    session = make_session()
    time.sleep(ARXIV_SLEEP_SECONDS)

    try:
        resp = session.get(endpoint, params=params, timeout=REQUEST_TIMEOUT)
    except requests.exceptions.RequestException as e:
        ARXIV_LAST_ERROR = True
        log(f"arXiv 网络异常: query={query}, err={e}")
        return []

    if resp.status_code != 200:
        ARXIV_LAST_ERROR = True
        log(f"arXiv 响应异常: status={resp.status_code}, query={query}, body={resp.text[:200]}")
        return []

    try:
        return parse_arxiv_atom(resp.text)
    except ET.ParseError as e:
        ARXIV_LAST_ERROR = True
        log(f"arXiv XML 解析失败: query={query}, err={e}")
        return []


def parse_arxiv_atom(xml_text: str) -> List[Dict[str, Any]]:
    ns = {
        "atom": "http://www.w3.org/2005/Atom",
        "arxiv": "http://arxiv.org/schemas/atom",
    }

    root = ET.fromstring(xml_text)
    papers = []

    for entry in root.findall("atom:entry", ns):
        title = normalize_text(entry.findtext("atom:title", default="", namespaces=ns))
        abstract = normalize_text(entry.findtext("atom:summary", default="", namespaces=ns))
        published = normalize_text(entry.findtext("atom:published", default="", namespaces=ns))
        updated = normalize_text(entry.findtext("atom:updated", default="", namespaces=ns))
        year = extract_year_from_date(published)

        entry_id = normalize_text(entry.findtext("atom:id", default="", namespaces=ns))
        arxiv_id = normalize_arxiv_id(entry_id) if entry_id else ""

        authors = []
        for a in entry.findall("atom:author", ns):
            name = normalize_text(a.findtext("atom:name", default="", namespaces=ns))
            if name:
                authors.append(name)

        pdf_url = ""
        page_url = entry_id
        for link in entry.findall("atom:link", ns):
            rel = link.attrib.get("rel", "")
            typ = link.attrib.get("type", "")
            href = link.attrib.get("href", "")
            title_attr = link.attrib.get("title", "")
            if rel == "alternate" and href:
                page_url = href
            if typ == "application/pdf" or title_attr == "pdf":
                pdf_url = href

        categories = []
        for cat in entry.findall("atom:category", ns):
            term = cat.attrib.get("term")
            if term:
                categories.append(term)

        doi = ""
        doi_node = entry.find("arxiv:doi", ns)
        if doi_node is not None and doi_node.text:
            doi = normalize_text(doi_node.text)

        papers.append({
            "source": ["arXiv"],
            "paperId": "",
            "title": title,
            "authors": authors,
            "year": year,
            "publicationDate": published[:10] if published else "",
            "updatedDate": updated[:10] if updated else "",
            "venue": "arXiv",
            "publicationVenue": None,
            "publicationTypes": ["Preprint"],
            "fieldsOfStudy": categories,
            "url": page_url,
            "pdfUrl": pdf_url,
            "doi": doi,
            "arxivId": arxiv_id,
            "citationCount": 0,
            "abstract": abstract,
            "queryCategories": [],
            "queries": [],
            "labels": [],
            "relevanceScore": 0,
            "relevanceReasons": [],
        })

    return papers


def normalize_arxiv_paper(
    raw: Dict[str, Any],
    category: str,
    query: str,
) -> Optional[Dict[str, Any]]:
    title = normalize_text(raw.get("title"))
    abstract = normalize_text(raw.get("abstract"))
    year = safe_year(raw.get("year"))

    if not title:
        return None
    if year and year < YEAR_FROM:
        return None

    score, reasons = compute_relevance_score(title, abstract, [category])
    included, screening_reasons = screen_paper(title, abstract, score)
    if not included:
        return None

    raw["queryCategories"] = [category]
    raw["queries"] = [query]
    raw["labels"] = classify_paper(title, abstract, [category])
    raw["relevanceScore"] = score
    raw["relevanceReasons"] = reasons + screening_reasons
    raw["screeningDecision"] = "included"
    raw["screeningReasons"] = screening_reasons

    return raw


# =========================================================
# 去重与合并
# =========================================================

def make_dedupe_key(p: Dict[str, Any]) -> str:
    doi = normalize_text(p.get("doi")).lower()
    arxiv_id = normalize_arxiv_id(p.get("arxivId") or "")
    paper_id = normalize_text(p.get("paperId")).lower()
    title = normalize_title(p.get("title") or "")

    if doi:
        return f"doi:{doi}"
    if arxiv_id:
        return f"arxiv:{arxiv_id}"
    if paper_id:
        return f"s2:{paper_id}"
    if title:
        return f"title:{title}"
    return f"unknown:{stable_hash(json.dumps(p, ensure_ascii=False, sort_keys=True))}"


def merge_paper(existing: Dict[str, Any], new: Dict[str, Any]) -> Dict[str, Any]:
    def merge_list(field: str) -> None:
        old = existing.get(field) or []
        add = new.get(field) or []
        if not isinstance(old, list):
            old = [old]
        if not isinstance(add, list):
            add = [add]
        merged = []
        for x in old + add:
            if x and x not in merged:
                merged.append(x)
        existing[field] = merged

    list_fields = [
        "source",
        "authors",
        "publicationTypes",
        "fieldsOfStudy",
        "queryCategories",
        "queries",
        "labels",
        "relevanceReasons",
        "screeningReasons",
    ]
    for field in list_fields:
        merge_list(field)

    for field in [
        "paperId", "title", "year", "publicationDate", "updatedDate", "venue",
        "url", "pdfUrl", "doi", "arxivId", "abstract", "screeningDecision"
    ]:
        if not existing.get(field) and new.get(field):
            existing[field] = new.get(field)

    existing["citationCount"] = max(
        int(existing.get("citationCount") or 0),
        int(new.get("citationCount") or 0)
    )

    existing["relevanceScore"] = max(
        int(existing.get("relevanceScore") or 0),
        int(new.get("relevanceScore") or 0)
    )

    if not existing.get("year") and new.get("year"):
        existing["year"] = new.get("year")

    return existing


def add_or_merge_paper(
    papers_by_key: Dict[str, Dict[str, Any]],
    paper: Dict[str, Any],
) -> None:
    key = make_dedupe_key(paper)
    if key in papers_by_key:
        papers_by_key[key] = merge_paper(papers_by_key[key], paper)
        return

    title_key = normalize_title(paper.get("title") or "")
    if title_key:
        for existing_key, existing_paper in papers_by_key.items():
            if normalize_title(existing_paper.get("title") or "") == title_key:
                papers_by_key[existing_key] = merge_paper(existing_paper, paper)
                return

    papers_by_key[key] = paper


# =========================================================
# 报告生成
# =========================================================

def format_authors(authors: List[str], max_authors: int = 6) -> str:
    if not authors:
        return "未知作者"
    if len(authors) <= max_authors:
        return ", ".join(authors)
    return ", ".join(authors[:max_authors]) + " et al."


def trim_abstract(abstract: str, max_len: int = 700) -> str:
    abstract = normalize_text(abstract)
    if not abstract:
        return "暂无摘要"
    if len(abstract) <= max_len:
        return abstract
    return abstract[:max_len].rstrip() + "..."


def build_markdown_report(
    papers: List[Dict[str, Any]],
    search_stats: List[Dict[str, Any]],
) -> str:
    lines = []

    lines.append("# 硬件代码缺陷检测/定位/修复系统性文献综述检索报告")
    lines.append("")
    lines.append(f"- 生成时间：{NOW_STR}")
    lines.append(f"- 年份范围：{YEAR_FROM}+")
    data_sources = "Semantic Scholar paper search"
    if ENABLE_ARXIV:
        data_sources += " + arXiv API"
    lines.append(f"- 数据源：{data_sources}")
    lines.append(
        "- 排除方向：纯软件代码缺陷、制造/图像/材料缺陷、纯 PPA/物理设计/"
        "后端优化/placement/routing/timing closure/ECO、无缺陷任务的硬件代码生成或优化"
    )
    lines.append(
        "- 初筛层级：标题/摘要自动初筛；最终纳入仍需人工全文复核"
    )
    lines.append(f"- 有效候选文献数：{len(papers)}")
    lines.append("")

    lines.append("## 一、检索协议")
    lines.append("")
    lines.append(f"- 研究问题：{REVIEW_QUESTION}")
    lines.append("- 纳入标准：")
    for item in INCLUSION_CRITERIA:
        lines.append(f"  - {item}")
    lines.append("- 排除标准：")
    for item in EXCLUSION_CRITERIA:
        lines.append(f"  - {item}")
    lines.append("")

    total_raw = sum(int(row.get("rawCount") or 0) for row in search_stats)
    total_screened_in = sum(int(row.get("includedRecords") or 0) for row in search_stats)
    total_unique_added = sum(int(row.get("uniqueAdded") or 0) for row in search_stats)

    lines.append("## 二、检索流程统计")
    lines.append("")
    lines.append("| 阶段 | 数量 |")
    lines.append("|---|---:|")
    lines.append(f"| 数据库返回原始记录 | {total_raw} |")
    lines.append(f"| 标题/摘要自动初筛纳入记录 | {total_screened_in} |")
    lines.append(f"| 自动去重后候选文献 | {len(papers)} |")
    lines.append(f"| 各检索式首次新增唯一记录合计 | {total_unique_added} |")
    lines.append("")

    label_count: Dict[str, int] = {}
    for p in papers:
        for label in p.get("labels") or ["待人工复核"]:
            label_count[label] = label_count.get(label, 0) + 1

    lines.append("## 三、分类统计")
    lines.append("")
    lines.append("| 类别 | 数量 |")
    lines.append("|---|---:|")
    for label, cnt in sorted(label_count.items(), key=lambda x: x[1], reverse=True):
        lines.append(f"| {label} | {cnt} |")
    lines.append("")

    top_papers = sorted(
        papers,
        key=lambda x: (
            int(x.get("relevanceScore") or 0),
            safe_year(x.get("year")),
            int(x.get("citationCount") or 0),
        ),
        reverse=True
    )[:30]

    lines.append("## 四、高相关论文 Top 30")
    lines.append("")
    lines.append("| 序号 | 年份 | 相关性 | 引用 | 类别 | 标题 |")
    lines.append("|---:|---:|---:|---:|---|---|")
    for i, p in enumerate(top_papers, 1):
        labels = "；".join(p.get("labels") or [])
        title = p.get("title") or "Untitled"
        url = p.get("url") or p.get("pdfUrl") or ""
        title_cell = f"[{title}]({url})" if url else title
        lines.append(
            f"| {i} | {p.get('year') or ''} | {p.get('relevanceScore') or 0} | "
            f"{p.get('citationCount') or 0} | {labels} | {title_cell} |"
        )
    lines.append("")

    sorted_papers = sorted(papers, key=paper_sort_key, reverse=True)

    lines.append("## 五、检索式记录")
    lines.append("")
    lines.append("| 数据源 | 类别 | 检索式 | 原始记录 | 初筛纳入 | 唯一新增 |")
    lines.append("|---|---|---|---:|---:|---:|")
    for row in search_stats:
        query = str(row.get("query") or "").replace("|", "\\|")
        lines.append(
            f"| {row.get('source') or ''} | {row.get('category') or ''} | "
            f"{query} | {row.get('rawCount') or 0} | "
            f"{row.get('includedRecords') or 0} | {row.get('uniqueAdded') or 0} |"
        )
    lines.append("")

    lines.append("## 六、详细文献列表")
    lines.append("")

    current_year = None
    for idx, p in enumerate(sorted_papers, 1):
        year = p.get("year") or "未知年份"
        if year != current_year:
            current_year = year
            lines.append(f"### {current_year}")
            lines.append("")

        title = p.get("title") or "Untitled"
        url = p.get("url") or ""
        pdf = p.get("pdfUrl") or ""
        labels = "；".join(p.get("labels") or ["待人工复核"])
        authors = format_authors(p.get("authors") or [])
        sources = " + ".join(p.get("source") or [])
        queries = "；".join(p.get("queries") or [])
        reasons = "；".join(p.get("relevanceReasons") or [])

        lines.append(f"#### {idx}. {title}")
        lines.append("")
        lines.append(f"- 作者：{authors}")
        lines.append(f"- 年份/日期：{p.get('year') or ''} / {p.get('publicationDate') or ''}")
        lines.append(f"- 来源：{sources}")
        lines.append(f"- Venue：{p.get('venue') or '未知'}")
        lines.append(f"- 类别：{labels}")
        lines.append(f"- 相关性评分：{p.get('relevanceScore') or 0}")
        lines.append(f"- 引用数：{p.get('citationCount') or 0}")
        if p.get("doi"):
            lines.append(f"- DOI：{p.get('doi')}")
        if p.get("arxivId"):
            lines.append(f"- arXiv ID：{p.get('arxivId')}")
        if url:
            lines.append(f"- 来源链接：[{url}]({url})")
        if pdf:
            lines.append(f"- PDF：[{pdf}]({pdf})")
        if queries:
            lines.append(f"- 命中查询：{queries}")
        if reasons:
            lines.append(f"- 入选原因：{reasons}")
        lines.append(f"- 摘要：{trim_abstract(p.get('abstract') or '')}")
        lines.append("")

    return "\n".join(lines)


# =========================================================
# 主流程
# =========================================================

def main() -> None:
    log("硬件代码缺陷检测/定位/修复系统性文献综述检索启动")
    log(f"年份范围: {YEAR_FROM}+")
    log(f"输出目录: {OUTPUT_DIR}")
    log(f"S2 API Key: {'已配置' if S2_API_KEY else '未配置，将使用匿名访问'}")
    log(f"绕过系统代理: {'是' if BYPASS_PROXY else '否'}")
    log(f"启用 arXiv: {'是' if ENABLE_ARXIV else '否'}")

    all_papers: Dict[str, Dict[str, Any]] = {}
    search_stats: List[Dict[str, Any]] = []
    raw_seen_count = 0
    arxiv_disabled = not ENABLE_ARXIV
    arxiv_error_streak = 0

    for category, terms in QUERY_MATRIX.items():
        log(f"开始类别: {category}, 查询数: {len(terms)}")

        for term in terms:
            # -------------------------------
            # Semantic Scholar
            # -------------------------------
            s2_query = quote_phrase_for_s2(term)
            log(f"S2 查询: {category} / {s2_query}")

            s2_raw_items = s2_search(s2_query)
            raw_seen_count += len(s2_raw_items)

            included_count = 0
            unique_before = len(all_papers)
            for raw in s2_raw_items:
                paper = normalize_s2_paper(raw, category, s2_query)
                if not paper:
                    continue
                included_count += 1
                add_or_merge_paper(all_papers, paper)
            search_stats.append({
                "source": "Semantic Scholar",
                "category": category,
                "query": s2_query,
                "rawCount": len(s2_raw_items),
                "includedRecords": included_count,
                "uniqueAdded": len(all_papers) - unique_before,
            })

            # -------------------------------
            # arXiv，可选，默认由 ENABLE_ARXIV 控制
            # -------------------------------
            if not arxiv_disabled:
                arxiv_query = build_arxiv_query(term)
                log(f"arXiv 查询: {category} / {term}")

                arxiv_raw_items = arxiv_search(arxiv_query)
                if ARXIV_LAST_ERROR:
                    arxiv_error_streak += 1
                else:
                    arxiv_error_streak = 0
                if arxiv_error_streak >= ARXIV_DISABLE_AFTER_ERRORS:
                    arxiv_disabled = True
                    log(
                        "arXiv 连续失败次数达到阈值，"
                        "本轮后续查询将跳过 arXiv"
                    )
                raw_seen_count += len(arxiv_raw_items)

                included_count = 0
                unique_before = len(all_papers)
                for raw in arxiv_raw_items:
                    paper = normalize_arxiv_paper(raw, category, arxiv_query)
                    if not paper:
                        continue
                    included_count += 1
                    add_or_merge_paper(all_papers, paper)
                search_stats.append({
                    "source": "arXiv",
                    "category": category,
                    "query": arxiv_query,
                    "rawCount": len(arxiv_raw_items),
                    "includedRecords": included_count,
                    "uniqueAdded": len(all_papers) - unique_before,
                })

    papers = list(all_papers.values())

    papers = sorted(
        papers,
        key=lambda x: (
            safe_year(x.get("year")),
            x.get("publicationDate") or "",
            int(x.get("relevanceScore") or 0),
            int(x.get("citationCount") or 0),
        ),
        reverse=True
    )

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    report_md = build_markdown_report(papers, search_stats)
    with open(REPORT_MD, "w", encoding="utf-8") as f:
        f.write(report_md)

    with open(REPORT_JSON, "w", encoding="utf-8") as f:
        json.dump({
            "generatedAt": NOW_STR,
            "yearFrom": YEAR_FROM,
            "excludedScope": [
                "software-only defect detection/localization/repair",
                "manufacturing/wafer/surface/visual/material defect inspection",
                "PPA closure",
                "physical design",
                "floorplanning",
                "placement",
                "routing",
                "timing closure",
                "ECO optimization",
                "post-layout/post-route backend optimization",
                "hardware-code generation/synthesis/verification without defect task",
            ],
            "rawSeenCount": raw_seen_count,
            "keptCount": len(papers),
            "reviewQuestion": REVIEW_QUESTION,
            "inclusionCriteria": INCLUSION_CRITERIA,
            "exclusionCriteria": EXCLUSION_CRITERIA,
            "queryMatrix": QUERY_MATRIX,
            "searchStats": search_stats,
            "papers": papers,
        }, f, ensure_ascii=False, indent=2)

    log("任务完成")
    log(f"原始候选数量: {raw_seen_count}")
    log(f"去重后有效数量: {len(papers)}")
    log(f"Markdown 报告: {REPORT_MD}")
    log(f"JSON 数据: {REPORT_JSON}")


if __name__ == "__main__":
    main()
