"""A compact decision surface over the complete statistical summary."""

import argparse
import re
import tomllib
from pathlib import Path
from urllib.parse import urlsplit

from bench.schema import Manifest, Precheck, Run, Summary

CANDIDATES = Path(__file__).resolve().parent / "candidates.toml"

# Parities whose timings may be compared with the baseline.
COMPARABLE = ("baseline", "identical", "sanctioned")


def actions_summary(results: Path, artifact_url: str) -> str:
    """Link bundled evidence to its download, keeping offline links untouched."""
    artifact = urlsplit(artifact_url)
    if artifact.scheme != "https" or not artifact.netloc:
        raise ValueError("the artifact download URL must be an absolute HTTPS URL")

    def evidence(match: re.Match[str]) -> str:
        label, target = match.groups()
        if urlsplit(target).scheme or target.startswith(("#", "//")):
            return match.group()
        if not (results / target).is_file():
            raise ValueError(f"linked evidence is missing from the artifact: {target}")
        return f'[{label}]({artifact_url} "{target}")'

    report = re.sub(
        r"\[([^\]]+)\]\(([^)]+)\)", evidence, (results / "report.md").read_text()
    )
    return (
        f"📦 [Download benchmark evidence]({artifact_url}). "
        "Evidence links download the ZIP; hover a link to see the file it points to inside. "
        "The bundled `report.md` links directly to those files.\n\n" + report
    )


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Publish an Actions-safe benchmark summary"
    )
    parser.add_argument("results", type=Path)
    parser.add_argument("--artifact-url", required=True)
    args = parser.parse_args(argv)
    print(actions_summary(args.results, args.artifact_url))


def count(number: int, noun: str) -> str:
    return f"{number} {noun}" if number == 1 else f"{number} {noun}s"


def duration(seconds: float) -> str:
    return f"{seconds * 1000:.2f} ms" if seconds < 1 else f"{seconds:.3f} s"


def workload(run: Run, name: str) -> str:
    scenario = run.scenarios[name]
    files = [arg for arg in scenario.args if arg in run.corpus.files]
    if not files:
        return scenario.description or name
    lines = sum(run.corpus.files[file] for file in files)
    size = (
        f"{lines:,}-line script"
        if len(files) == 1
        else f"{len(files):,} scripts ({lines:,} lines total)"
    )
    output = {"gcc": "GCC diagnostics", "json1": "JSON diagnostics"}.get(
        scenario.format, f"{scenario.format} output"
    )
    context = f"{scenario.label} · " if scenario.label else ""
    return f"{context}{size} · {output}"


def brief(run: Run, name: str, *extra: str) -> str:
    """The workload's label and output format, or its full title when it has no
    label, with `extra` appended in parentheses."""
    scenario = run.scenarios[name]
    if not scenario.label:
        return f"**{workload(run, name)}**" + (
            f" ({', '.join(extra)})" if extra else ""
        )
    output = {"gcc": "GCC", "json1": "JSON"}.get(scenario.format, scenario.format)
    return f"**{scenario.label}** ({', '.join((output, *extra))})"


def quality(flags: list[str]) -> list[str]:
    """Short names of the measurement-quality flags in `flags`."""
    names = {"noisy": "noisy", "drift": "drift", "only ": "few samples"}
    return [
        word
        for prefix, word in names.items()
        if any(flag.startswith(prefix) for flag in flags)
    ]


def stopped(reason: str) -> str:
    """The status of a cell whose sampling stopped early."""
    first = reason.split("; ", 1)[0]
    # `measure.Budget.reason` opens with these words.
    return (
        "budget spent"
        if first.startswith("total candidate measurement budget")
        else first
    )


def label(candidate: Manifest) -> str:
    """The candidate's display name. An `upstream-` candidate carries the
    revision it measured, since its name alone does not say which ShellCheck
    that was."""
    if not candidate.name.startswith("upstream-") or not candidate.pin:
        return candidate.name
    if candidate.kind == "release":
        return f"{candidate.name}-v{candidate.pin.removeprefix('v')}"
    if candidate.kind == "git":
        return f"{candidate.name}-{candidate.pin[:7]}"
    return candidate.name


def ordered(run: Run) -> list[Manifest]:
    """Candidates in the order candidates.toml lists them; any candidate the
    file no longer names follows in run order."""
    with CANDIDATES.open("rb") as file:
        rank = {name: i for i, name in enumerate(tomllib.load(file)["candidates"])}
    return sorted(run.candidates, key=lambda c: rank.get(c.name, len(rank)))


def once(check: Precheck) -> bool:
    """Whether a correct pre-check run was the only timing of this cell."""
    return check.status == "slow"


def project(candidate: Manifest) -> str | None:
    """The candidate's repository URL without a trailing slash or `.git`."""
    return candidate.repo.rstrip("/").removesuffix(".git") if candidate.repo else None


def revision(candidate: Manifest) -> str:
    label = candidate.pin[:12] or "supplied binary"
    repo = project(candidate)
    if repo and repo.startswith("https://github.com/"):
        if candidate.kind == "git" and candidate.pin:
            return f"[{label}]({repo}/commit/{candidate.pin})"
        if candidate.kind == "release" and candidate.pin:
            return f"[{label}]({repo}/releases/tag/v{candidate.pin.removeprefix('v')})"
    return label


def render(run: Run, summary: Summary, plot_paths: dict[str, str] | None = None) -> str:
    baseline = run.baseline
    candidates = ordered(run)
    names = [candidate.name for candidate in candidates]
    shown = {candidate.name: label(candidate) for candidate in candidates}

    def observed(scenario: str, name: str) -> float | None:
        """The median, or the single pre-check time of a cell timed once."""
        cell = summary.descriptives[scenario][name]
        if cell:
            return cell.median
        check = run.precheck[scenario][name]
        if once(check) or run.samples[scenario][name].stop_reason:
            return check.wall_s
        return None

    comparisons = {
        (pair.scenario, pair.candidate): pair
        for pair in summary.comparisons
        if pair.reference == baseline
    }
    lines = [
        f"# 🏁 ShellCheck benchmark: {run.created[:10]}",
        "",
    ]
    for name, source in run.corpus.sources.items():
        files = {
            file: count
            for file, count in run.corpus.files.items()
            if file.startswith(source.prefix + "/")
        }
        repo = source.repo.rstrip("/").removesuffix(".git")
        file_label = "shell file" if len(files) == 1 else "shell files"
        lines += [
            (
                f"**{name.title()}**: [{source.pin[:12]}]({repo}/commit/{source.pin}); "
                f"**{len(files):,} {file_label}, {sum(files.values()):,} lines**."
            ),
            "",
        ]
    for note in run.notes:
        # `candidates.plan` writes full commit hashes into its notes.
        note = re.sub(r"\b[0-9a-f]{40}\b", lambda sha: f"`{sha[0][:12]}`", note)
        lines += ["> [!NOTE]", f"> {note}", ""]
    lines += [
        "## Where to look first",
        "",
        f"Baseline: **{shown[baseline]}**. Ratios are candidate ÷ baseline; higher means more cost.",
        "",
    ]
    actions: list[str] = []
    reference = project(next(c for c in candidates if c.name == baseline))
    for candidate in candidates:
        name = candidate.name
        if name == baseline:
            continue
        # Another build of the baseline's project differs from it by upstream's
        # own changes; its comparisons stay in the tables.
        upstream = reference is not None and project(candidate) == reference
        reliable: list[tuple[float, str]] = []
        memory: list[tuple[float, str, float]] = []
        differs: list[str] = []
        limited: list[str] = []
        failed: list[str] = []
        for scenario in run.scenarios:
            check = run.precheck[scenario][name]
            cell = summary.descriptives[scenario][name]
            base = summary.descriptives[scenario][baseline]
            flags = summary.flags[scenario][name] + summary.flags[scenario][baseline]
            if check.parity == "differs" and not upstream:
                differs.append(
                    brief(run, scenario, f"[diff](precheck/{scenario}/{name}.diff)")
                )
            if check.status == "limited":
                limited.append(brief(run, scenario))
            elif check.status == "failed":
                failed.append(
                    f"**{shown[name]}**, {brief(run, scenario)}: investigate {check.reason}."
                )
            if (
                upstream
                or not cell
                or not base
                or check.parity not in ("identical", "sanctioned")
            ):
                continue
            pair = comparisons.get((scenario, name))
            unstable = any(
                flag.startswith((
                    "noisy",
                    "drift",
                    "only ",
                    "excluded",
                    "timed once",
                    "not comparable",
                ))
                for flag in flags
            )
            if pair and pair.verdict == "slower" and not unstable and base.median:
                reliable.append((cell.median / base.median, scenario))
            if base.peak_rss_median:
                memory.append((
                    cell.peak_rss_median / base.peak_rss_median,
                    scenario,
                    cell.peak_rss_median,
                ))
        if differs:
            actions.append(
                f"**{shown[name]}**: output differs on {', '.join(differs)}. "
                "Read the diffs before its timings."
            )
        if limited:
            actions.append(
                f"**{shown[name]}**: the measurement budget ran out during {', '.join(limited)}; "
                "output agreement there is unknown."
            )
        actions += failed
        if reliable:
            ratio, scenario = max(reliable)
            cell = summary.descriptives[scenario][name]
            base = summary.descriptives[scenario][baseline]
            assert cell and base
            actions.append(
                f"**{shown[name]}**: profile {brief(run, scenario)}: "
                f"**{duration(cell.median)}** against {shown[baseline]} **{duration(base.median)}** "
                f"(**{ratio:.2f}×** time)."
            )
        if memory:
            ratio, scenario, rss = max(memory)
            if ratio > 1:
                actions.append(
                    f"**{shown[name]}**: highest memory ratio on {brief(run, scenario)}: "
                    f"**{rss / 2**20:.0f} MiB**, **{ratio:.2f}×** baseline."
                )
    if actions:
        lines += [f"- {action}" for action in actions[:8]]
        if len(actions) > 8:
            lines.append(
                f"- {len(actions) - 8} further issues appear in the table and summary.json."
            )
    else:
        lines.append(
            "No clear performance priority from this run; inspect measurement status before drawing conclusions."
        )
    config = run.config
    budgets = sorted(
        {
            scenario.max_run_seconds or config.max_run_s
            for scenario in run.scenarios.values()
        }
        - {0}
    )
    limits = ", ".join(f"{budget:g}s" for budget in budgets)
    per_run = f"per-run budget ({limits})" if limits else "per-run budget"
    lines += [
        "",
        "## The results",
        "",
        (
            "- 🏆 marks the lowest median of a table when that candidate's output matches and at least two candidates match. "
            "A table whose fastest candidate differs in output or ran once awards no trophy."
        ),
        (
            "- **faster** and **slower** are significant verdicts. **noisy**, **drift** or **few samples** "
            "after a verdict flag an unsteady measurement; alone they ask for a repeat."
        ),
        (
            f"- **timed once**: one run took longer than the {per_run}, so the candidate ran once. "
            "**baseline timed once**: the ratio divides by that single baseline run. "
            "≈ marks such a ratio, which has no interval."
        ),
        "- **budget spent**: the candidate's total measurement budget ran out before or during this workload.",
    ]
    for scenario in run.scenarios:
        lines += [
            "",
            f"### {workload(run, scenario)}",
            "",
            "| candidate | output | median | time ratio [95% CI] | peak RSS | RSS ratio | status |",
            "|---|---|---:|---:|---:|---:|---|",
        ]
        sanctioned: list[str] = []
        base = summary.descriptives[scenario][baseline]
        base_check = run.precheck[scenario][baseline]
        base_value = observed(scenario, baseline)
        eligible = {
            name: value
            for name in names
            if (value := observed(scenario, name)) is not None
            and run.precheck[scenario][name].status in ("ok", "slow")
            and run.precheck[scenario][name].parity in COMPARABLE
            and not any(
                flag.startswith("not comparable")
                for flag in summary.flags[scenario][name]
            )
        }
        # Only the fastest candidate that ran can earn the trophy, and it
        # needs a median: a runner-up is a slower tool.
        ran = {
            name: value
            for name in names
            if (value := observed(scenario, name)) is not None
            and run.precheck[scenario][name].status in ("ok", "slow")
        }
        fastest = min(ran, key=ran.__getitem__) if ran else None
        winner = (
            fastest
            if fastest in eligible
            and len(eligible) > 1
            and summary.descriptives[scenario][fastest]
            else None
        )
        for name in names:
            check = run.precheck[scenario][name]
            cell = summary.descriptives[scenario][name]
            flags = summary.flags[scenario][name]
            pair = comparisons.get((scenario, name))
            value = observed(scenario, name)
            diff = f"[diff](precheck/{scenario}/{name}.diff)"
            output = {
                "baseline": "baseline",
                "identical": "matches",
                # The judge compares findings. Equal findings can differ in
                # bytes: the port's json1 adds a `sources` member.
                "sanctioned": f"sanctioned ({diff})"
                if check.deviations
                else f"same findings ({diff})",
                "unknown": "unknown",
                "differs": f"differs ({diff})",
            }[check.parity]
            if check.parity == "sanctioned" and check.deviations:
                sanctioned.append(
                    f"{shown[name]} "
                    + ", ".join(f"`{deviation}`" for deviation in check.deviations)
                )
            median = (
                duration(cell.median)
                if cell
                else duration(check.wall_s)
                if once(check) or run.samples[scenario][name].stop_reason
                else duration(check.wall_s) + " (stopped)"
                if check.status == "limited"
                else "-"
            )
            ratio = "-"
            if cell and base and base.median:
                ratio = f"{cell.median / base.median:.2f}×"
                if pair:
                    low, high = pair.speedup_median_ci
                    if low > 0:
                        ratio += f" [{1 / high:.2f}, {1 / low:.2f}]"
            elif name == baseline and base_value:
                ratio = "1.00×"
            elif value is not None and base_value:
                # One side was timed once: a point ratio, never an interval.
                ratio = f"≈{value / base_value:.2f}×"
            rss = cell.peak_rss_median if cell else check.peak_rss_bytes
            completed = check.status in ("ok", "slow")
            base_rss = (
                base.peak_rss_median
                if base
                else base_check.peak_rss_bytes
                if base_check.status in ("ok", "slow")
                else 0
            )
            if cell and base and base_rss:
                rss_ratio = f"{rss / base_rss:.2f}×"
            elif (cell or completed) and base_rss:
                # One side has only its pre-check peak: a point ratio.
                rss_ratio = f"≈{rss / base_rss:.2f}×"
            else:
                rss_ratio = "-"
            base_flags = summary.flags[scenario][baseline]
            unsteady = quality(flags + base_flags)
            if stop := run.samples[scenario][name].stop_reason:
                status = stopped(stop)
            elif check.status == "slow":
                status = "timed once"
            elif check.status in ("limited", "skipped"):
                status = "budget spent"
            elif check.status != "ok":
                status = check.reason or check.status
            elif check.parity not in COMPARABLE or any(
                flag.startswith("not comparable") for flag in flags + base_flags
            ):
                status = "not comparable"
            elif once(base_check) and name != baseline:
                status = "baseline timed once"
            # `analyze.verdict` grants these only with an interval excluding 1
            # and a Holm-adjusted p < 0.05, both computed over the noisy samples.
            elif pair and pair.verdict in ("faster", "slower"):
                status = pair.verdict + (
                    f" ({', '.join(unsteady)})" if unsteady else ""
                )
            elif unsteady:
                status = (
                    "repeat: noise/drift"
                    if {"noisy", "drift"} & set(unsteady)
                    else "repeat: few samples"
                )
            elif name == baseline:
                status = "reference"
            elif pair:
                status = pair.verdict
            else:
                status = "not comparable"
            if name == winner:
                median = f"**🏆 {median}**"
            rss_text = "-" if check.status == "skipped" else f"{rss / 2**20:.0f} MiB"
            lines.append(
                f"| {shown[name]} | {output} | {median} | {ratio} | {rss_text} | {rss_ratio} | {status} |"
            )
        if sanctioned:
            lines += ["", f"Sanctioned deviations: {'; '.join(sanctioned)}."]
    lines += [
        "",
        "## Candidates",
        "",
        "| candidate | revision | binary | SHA-256 |",
        "|---|---|---:|---|",
    ]
    for candidate in candidates:
        dirty = " + local changes" if candidate.dirty else ""
        lines.append(
            f"| {shown[candidate.name]} | {revision(candidate)}{dirty} | "
            f"{candidate.binary_bytes / 2**20:.1f} MiB | "
            f"[{candidate.binary_sha256[:12]}](run.json) |"
        )
    for name, limit in config.candidate_budget_s.items():
        lines += [
            "",
            f"**{shown.get(name, name)} total measurement budget: {limit:g}s**; used **{run.candidate_elapsed_s.get(name, 0):.1f}s** across initial checks, warm-ups and timed runs. Compilation is separate.",
        ]
    lines += [
        "",
        (
            f"{count(config.rounds, 'shuffled round')} × {count(config.runs, 'timed run')}, "
            f"{count(config.warmup, 'warm-up')} per round. "
            f"Seed {config.seed}; corpus [{run.corpus.sha256[:12]}](run.json). "
            f"CPU: {run.environment.cpu_model or 'unknown'}; {'CPU ' + config.pin if config.pin else 'no CPU pinning'}."
        ),
        "",
        (
            "Time intervals use seeded bootstrap resampling. Verdicts require an interval excluding 1 and a Holm-adjusted Mann–Whitney p < 0.05. "
            "Mismatched output earns no speed verdict. RSS is the median of isolated per-round process peaks; failed and single-run rows show the pre-check peak."
        ),
        "",
        (
            "Evidence: [raw run](run.json), [all statistics and quality flags](summary.json), `raw/`, and `precheck/`. "
            "Rebuild this report with `uvx --from git+https://github.com/kjanat/shellcheck-rs@bench bench report <directory>`."
        ),
        "",
    ]
    if plot_paths:
        lines += [
            "Timing plots: "
            + ", ".join(f"[{name}]({path})" for name, path in plot_paths.items()),
            "",
        ]
    return "\n".join(lines)
