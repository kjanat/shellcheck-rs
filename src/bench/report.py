"""A compact decision surface over the complete statistical summary."""

from bench.schema import Manifest, Run, Summary


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


def revision(candidate: Manifest) -> str:
    label = candidate.pin[:12] or "supplied binary"
    if candidate.repo and candidate.repo.startswith("https://github.com/"):
        repo = candidate.repo.rstrip("/").removesuffix(".git")
        if candidate.kind == "git" and candidate.pin:
            return f"[{label}]({repo}/commit/{candidate.pin})"
        if candidate.kind == "release" and candidate.pin:
            return f"[{label}]({repo}/releases/tag/v{candidate.pin.removeprefix('v')})"
    return label


def render(run: Run, summary: Summary, plot_paths: dict[str, str] | None = None) -> str:
    baseline = run.baseline
    names = [candidate.name for candidate in run.candidates]
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
    lines += [
        "## Where to look first",
        "",
        f"Baseline: **{baseline}**. Ratios are candidate ÷ baseline; higher means more cost.",
        "",
    ]
    actions: list[str] = []
    for name in names:
        if name == baseline:
            continue
        reliable: list[tuple[float, str]] = []
        memory: list[tuple[float, str, float]] = []
        for scenario in run.scenarios:
            check = run.precheck[scenario][name]
            cell = summary.descriptives[scenario][name]
            base = summary.descriptives[scenario][baseline]
            flags = summary.flags[scenario][name] + summary.flags[scenario][baseline]
            if check.parity == "differs":
                actions.append(
                    f"{name}, **{workload(run, scenario)}**: inspect the [output diff](precheck/{scenario}/{name}.diff) before interpreting performance."
                )
            if check.status == "limited":
                actions.append(
                    f"{name}, **{workload(run, scenario)}**: this workload stopped at the total measurement budget; its output agreement is unknown."
                )
            elif check.status == "failed":
                actions.append(
                    f"{name}, **{workload(run, scenario)}**: investigate {check.reason}."
                )
            if not cell or not base or check.parity != "identical":
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
        if reliable:
            ratio, scenario = max(reliable)
            cell = summary.descriptives[scenario][name]
            base = summary.descriptives[scenario][baseline]
            assert cell and base
            actions.append(
                f"{name}: profile the **{workload(run, scenario)}**: "
                f"**{duration(cell.median)}** vs {baseline} **{duration(base.median)}** "
                f"(**{ratio:.2f}× time**)."
            )
        if memory:
            ratio, scenario, rss = max(memory)
            if ratio > 1:
                actions.append(
                    f"{name}: largest observed memory ratio is on the **{workload(run, scenario)}** "
                    f"(**{rss / 2**20:.0f} MiB**, **{ratio:.2f}× baseline**)."
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
    lines += [
        "",
        "## The results",
        "",
        "🏆 marks the lowest observed median with matching output. Noise and statistical significance appear in the status column.",
    ]
    for scenario in run.scenarios:
        lines += [
            "",
            f"### {workload(run, scenario)}",
            "",
            "| candidate | output | median | time / baseline [95% CI] | peak RSS | RSS / baseline | status |",
            "|---|---|---:|---:|---:|---:|---|",
        ]
        base = summary.descriptives[scenario][baseline]
        eligible = {
            name: cell.median
            for name in names
            if (cell := summary.descriptives[scenario][name]) is not None
            and run.precheck[scenario][name].status == "ok"
            and run.precheck[scenario][name].parity in ("baseline", "identical")
            and not any(
                flag.startswith("not comparable")
                for flag in summary.flags[scenario][name]
            )
        }
        winner = min(eligible, key=eligible.__getitem__, default=None)
        for name in names:
            check = run.precheck[scenario][name]
            cell = summary.descriptives[scenario][name]
            flags = summary.flags[scenario][name]
            pair = comparisons.get((scenario, name))
            output = {
                "baseline": "baseline",
                "identical": "matches",
                "unknown": "unknown",
                "differs": f"[diff](precheck/{scenario}/{name}.diff)",
            }[check.parity]
            median = (
                duration(cell.median)
                if cell
                else duration(check.wall_s) + " (once)"
                if check.status == "slow" or run.samples[scenario][name].stop_reason
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
            rss = cell.peak_rss_median if cell else check.peak_rss_bytes
            rss_ratio = (
                f"{rss / base.peak_rss_median:.2f}×"
                if cell and base and base.peak_rss_median
                else "-"
            )
            unstable = any(
                flag.startswith(("noisy", "drift", "only ")) for flag in flags
            )
            base_flags = summary.flags[scenario][baseline]
            base_unstable = any(
                flag.startswith(("noisy", "drift", "only ")) for flag in base_flags
            )
            if run.samples[scenario][name].stop_reason:
                status = run.samples[scenario][name].stop_reason
            elif check.status != "ok":
                status = check.reason or check.status
            elif check.parity not in ("baseline", "identical") or any(
                flag.startswith("not comparable") for flag in flags + base_flags
            ):
                status = "not comparable"
            elif unstable or base_unstable:
                status = (
                    "repeat: noise/drift"
                    if any(
                        flag.startswith(("noisy", "drift"))
                        for flag in flags + base_flags
                    )
                    else "repeat: few samples"
                )
            elif name == baseline:
                status = "reference"
            elif pair:
                status = pair.verdict
            else:
                status = "not comparable"
            if name == winner:
                median = f"***🏆 {median}***"
            rss_text = "-" if check.status == "skipped" else f"{rss / 2**20:.0f} MiB"
            lines.append(
                f"| {name} | {output} | {median} | {ratio} | {rss_text} | {rss_ratio} | {status} |"
            )
    lines += ["", "Candidates:", ""]
    for candidate in run.candidates:
        dirty = " + local changes" if candidate.dirty else ""
        lines.append(
            f"- **{candidate.name}**: {revision(candidate)}{dirty}; "
            f"{candidate.binary_bytes / 2**20:.1f} MiB binary; "
            f"SHA-256 [{candidate.binary_sha256[:12]}](run.json)."
        )
    config = run.config
    for name, limit in config.candidate_budget_s.items():
        lines += [
            "",
            f"**{name} total measurement budget: {duration(limit)}**; used **{duration(run.candidate_elapsed_s.get(name, 0))}** across initial checks, warm-ups and timed runs. Compilation is separate. Budget-limited and skipped workloads are marked above.",
        ]
    budgets = sorted(
        {
            scenario.max_run_seconds or config.max_run_s
            for scenario in run.scenarios.values()
        }
        - {0}
    )
    if budgets:
        lines += [
            "",
            "Per-run sampling budgets: "
            + ", ".join(f"**{budget:g}s**" for budget in budgets)
            + ". Over-budget candidates are reported once, without a timing confidence interval.",
        ]
    lines += [
        "",
        (
            f"{config.rounds} shuffled rounds × {config.runs} timed runs, {config.warmup} warm-ups per round. "
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
            "Rebuild this report with `uv run bench report <directory>`."
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
