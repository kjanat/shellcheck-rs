from typing import Literal

from pydantic import BaseModel, Field, computed_field, model_validator

type Kind = Literal["release", "git", "path"]
type Status = Literal["ok", "slow", "failed"]
type Parity = Literal["baseline", "identical", "differs", "unknown"]


class CandidateSpec(BaseModel):
    binary: str = "rshellcheck"
    baseline: bool = False
    repo: str | None = None
    ref: str = ""
    package: str = ""
    tools: list[str] = []
    tool: str | None = None
    jobs: int = Field(default=2, ge=1)


class CandidatesFile(BaseModel):
    candidates: dict[str, CandidateSpec]


class Manifest(BaseModel):
    name: str
    kind: Kind
    ref: str
    pin: str
    binary: str
    binary_sha256: str
    binary_bytes: int
    version_output: str
    repo: str | None = None
    source: str | None = None
    dirty: bool = False
    source_sha256: str | None = None
    build_key: str | None = None


class ScenarioSpec(BaseModel):
    description: str = ""
    args: list[str]


class ScenariosFile(BaseModel):
    scenarios: dict[str, ScenarioSpec]


class Scenario(BaseModel):
    description: str
    args: list[str]
    format: str


class CorpusFile(BaseModel):
    sha256: str
    lines: int
    bytes: int


class CorpusManifest(BaseModel):
    seed: int
    generator: str
    files: dict[str, CorpusFile]
    sha256: str


class CorpusRef(BaseModel):
    dir: str
    sha256: str
    seed: int
    files: dict[str, int]


class HyperfineResult(BaseModel):
    command: str
    mean: float
    user: float
    system: float
    times: list[float]
    memory_usage_byte: list[int] = []
    exit_codes: list[int | None] = []


class Metric(BaseModel):
    value: float
    unit: str | None = None


class Measurement(BaseModel):
    time_wall_clock: Metric
    time_user: Metric
    time_system: Metric
    memory_peak_resident: Metric | None = None
    exit_code: int | None = None


class ModernResult(BaseModel):
    command: str
    measurements: list[Measurement]


class ModernExport(BaseModel):
    schema_version: Literal[2]
    results: list[ModernResult]


class HyperfineExport(BaseModel):
    results: list[HyperfineResult]

    @model_validator(mode="before")
    @classmethod
    def normalize(cls, value: object) -> object:
        if not isinstance(value, dict) or "schema_version" not in value:
            return value
        modern = ModernExport.model_validate(value)
        results: list[HyperfineResult] = []
        for result in modern.results:
            if not result.measurements:
                raise ValueError("hyperfine returned no measurements")
            for measurement in result.measurements:
                for metric in (
                    measurement.time_wall_clock,
                    measurement.time_user,
                    measurement.time_system,
                ):
                    if metric.unit != "second" or metric.value < 0:
                        raise ValueError(
                            "hyperfine time metrics must be nonnegative seconds"
                        )
                if measurement.memory_peak_resident and (
                    measurement.memory_peak_resident.unit != "byte"
                    or measurement.memory_peak_resident.value < 0
                ):
                    raise ValueError(
                        "hyperfine memory metrics must be nonnegative bytes"
                    )
            count = len(result.measurements)
            results.append(
                HyperfineResult(
                    command=result.command,
                    mean=sum(item.time_wall_clock.value for item in result.measurements)
                    / count,
                    user=sum(item.time_user.value for item in result.measurements)
                    / count,
                    system=sum(item.time_system.value for item in result.measurements)
                    / count,
                    times=[item.time_wall_clock.value for item in result.measurements],
                    memory_usage_byte=[
                        int(item.memory_peak_resident.value)
                        for item in result.measurements
                        if item.memory_peak_resident
                    ],
                    exit_codes=[item.exit_code for item in result.measurements],
                )
            )
        return {"results": results}


class Environment(BaseModel):
    hostname: str
    kernel: str
    os: str
    arch: str
    python: str
    cpu_count: int | None
    ci: bool
    github: dict[str, str]
    hyperfine: str | None
    cpu_model: str | None = None
    mem_total_kib: int | None = None
    loadavg_at_start: tuple[float, float, float] | None = None
    cpu_governor: str | None = None


class Config(BaseModel):
    rounds: int
    runs: int
    warmup: int
    seed: int
    pin: str | None
    max_rss_gib: float
    timeout_s: float
    max_run_s: float = 0.0
    hyperfine_flags: list[str]
    memory_isolated: bool = False


class Precheck(BaseModel):
    exit: int | None
    signal: int | None
    wall_s: float
    peak_rss_bytes: int
    killed: str | None
    stdout_bytes: int
    stdout_sha256: str
    stderr_head: str
    status: Status
    reason: str | None
    parity: Parity
    diff_lines: int | None = None


class Round(BaseModel):
    round: int
    position: int
    times: list[float]
    memory_bytes: list[int] = []
    user_mean: float | None = None
    system_mean: float | None = None


class Samples(BaseModel):
    times: list[float] = []
    memory_bytes: list[int] = []
    exit_codes: list[int | None] = []
    rounds: list[Round] = []

    @computed_field
    @property
    def n(self) -> int:
        return len(self.times)


class Run(BaseModel):
    version: int
    created: str
    config: Config
    environment: Environment
    baseline: str
    candidates: list[Manifest]
    corpus: CorpusRef
    scenarios: dict[str, Scenario]
    precheck: dict[str, dict[str, Precheck]]
    samples: dict[str, dict[str, Samples]]
    elapsed_s: float


type Verdict = Literal["faster", "slower", "no significant difference", "n/a"]


class Descriptives(BaseModel):
    n: int
    mean: float
    sd: float
    cv: float
    sem: float
    median: float
    mad: float
    min: float
    max: float
    p5: float
    p95: float
    ci_mean: tuple[float, float]
    ci_median: tuple[float, float]
    outliers: int
    outlier_frac: float
    peak_rss_median: float
    peak_rss_source: str
    exit_codes: list[int | None]
    drift_p: float | None
    drift_spread: float


class Comparison(BaseModel):
    speedup_mean: float
    speedup_mean_ci: tuple[float, float]
    speedup_median: float
    speedup_median_ci: tuple[float, float]
    diff_mean: float
    welch_p: float
    mwu_p: float
    cliffs_delta: float
    hedges_g: float
    scenario: str
    candidate: str
    reference: str
    mwu_p_adj: float
    welch_p_adj: float
    verdict: Verdict
    verdict_detail: str


class CandidateSummary(BaseModel):
    kind: Kind
    ref: str
    pin: str
    dirty: bool = False
    source_sha256: str | None = None
    build_key: str | None = None
    binary_sha256: str
    binary_bytes: int
    version_output: str


class Summary(BaseModel):
    version: int = 1
    results_dir: str
    created: str
    baseline: str
    alpha: float
    resamples: int
    candidates: dict[str, CandidateSummary]
    descriptives: dict[str, dict[str, Descriptives | None]]
    flags: dict[str, dict[str, list[str]]]
    comparisons: list[Comparison]
    environment: Environment
    config: Config
    corpus: CorpusRef
