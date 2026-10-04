from typing import Annotated, Literal

from pydantic import BaseModel, Field, computed_field

type Kind = Literal["release", "git"]
type Status = Literal["ok", "slow", "failed"]
type Parity = Literal["baseline", "identical", "differs", "unknown"]


class ReleaseSpec(BaseModel):
    kind: Literal["release"]
    baseline: bool = False


class GitSpec(BaseModel):
    kind: Literal["git"]
    ref: str
    build: str
    baseline: bool = False


type CandidateSpec = Annotated[ReleaseSpec | GitSpec, Field(discriminator="kind")]


class CandidatesFile(BaseModel):
    candidates: dict[str, CandidateSpec]


class Manifest(BaseModel):
    name: str
    kind: Kind
    ref: str
    pin: str
    key: str
    binary: str
    binary_sha256: str
    binary_bytes: int
    version_output: str
    toolchain: list[str]
    built_at: str
    built_on: str


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


class HyperfineExport(BaseModel):
    results: list[HyperfineResult]


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
