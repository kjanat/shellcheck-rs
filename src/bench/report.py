"""A compact decision surface over the complete statistical summary."""

from bench.schema import Run, Summary


def duration(seconds: float) -> str:
    return f"{seconds * 1000:.2f} ms" if seconds < 1 else f"{seconds:.3f} s"


def render(run: Run, summary: Summary, plot_paths: dict[str, str] | None = None) -> str:
    baseline = run.baseline
    names = [candidate.name for candidate in run.candidates]
    comparisons = {
        (pair.scenario, pair.candidate): pair
        for pair in summary.comparisons
        if pair.reference == baseline
    }
    lines = [
        f"# ShellCheck benchmark: {run.created[:10]}",
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
                    f"{name}/{scenario}: inspect the [output diff](precheck/{scenario}/{name}.diff) before interpreting performance."
                )
            if check.status == "failed":
                actions.append(f"{name}/{scenario}: investigate {check.reason}.")
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
            actions.append(
                f"{name}: investigate runtime on **{scenario}** ({ratio:.2f}× baseline)."
            )
        if memory:
            ratio, scenario, rss = max(memory)
            if ratio > 1:
                actions.append(
                    f"{name}: largest observed memory ratio is **{scenario}** ({ratio:.2f}× baseline, {rss / 2**20:.0f} MiB)."
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
        "| candidate | workload | output | median | time / baseline [95% CI] | peak RSS | RSS / baseline | status |",
        "|---|---|---|---:|---:|---:|---:|---|",
    ]
    for scenario in run.scenarios:
        base = summary.descriptives[scenario][baseline]
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
                if check.status == "slow"
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
            if check.status != "ok":
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
            lines.append(
                f"| {name} | {scenario} | {output} | {median} | {ratio} | {rss / 2**20:.0f} MiB | {rss_ratio} | {status} |"
            )
    lines += ["", "Candidates:", ""]
    for candidate in run.candidates:
        revision = candidate.pin[:12] or "supplied binary"
        dirty = " + local changes" if candidate.dirty else ""
        lines.append(
            f"- **{candidate.name}**: `{revision}`{dirty}; {candidate.binary_bytes / 2**20:.1f} MiB binary; SHA-256 `{candidate.binary_sha256}`."
        )
    config = run.config
    lines += [
        "",
        (
            f"{config.rounds} shuffled rounds × {config.runs} timed runs, {config.warmup} warm-ups per round. "
            f"Seed {config.seed}; corpus `{run.corpus.sha256[:12]}`. "
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
