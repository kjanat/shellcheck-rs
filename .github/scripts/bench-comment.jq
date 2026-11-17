# Renders the head of the Bench pull request comment from `summary.json`.
# Usage: jq -r --arg pr N --slurpfile run run.json -f bench-comment.jq summary.json
def f2: (. * 100 | round) as $n | "\($n / 100 | floor).\($n % 100 | tostring | if length < 2 then "0" + . else . end)";
def percent: (. - 1) * 1000 | round / 10 | if . == 0 then 0 else . end;
def name($s): $run[0].scenarios[$s] as $x
  | (if $x.label != "" then $x.label else $s end) + " (" + ({gcc: "GCC", json1: "JSON"}[$x.format] // $x.format) + ")";
def bounds: (min / 5 | floor) * 5 - 5, (max / 5 | ceil) * 5 + 5;
def chart($title; $axis; $series):
  ([$series[].values[]] + [0]) as $all
  | [$all | bounds] as [$low, $high]
  | "```mermaid",
    "---",
    "config:",
    "  xyChart:",
    "    width: 900",
    "    height: 320",
    "---",
    "xychart-beta",
    "    title \"\($title)\"",
    "    x-axis [\($axis | map("\"\(.)\"") | join(", "))]",
    "    y-axis \"%\" \($low) --> \($high)",
    ($series[] | "    \(.kind) \"\(.name)\" [\(.values | map(tostring) | join(", "))]"),
    "```";
.descriptives as $descriptives
| [.comparisons[] | select(.candidate == "pr" and .reference == "master")] as $pairs
| [$pairs[] | select(.verdict == "slower" or .verdict == "faster")] as $changed
| [$run[0].precheck | to_entries[] | select(.value.pr.parity == "differs" or .value.pr.parity == "unknown") | .key] as $differs
| [$pairs[] | .scenario as $s | $descriptives[$s] | select(.pr != null and .master != null)
    | {s: $s, r: (.pr.peak_rss_median / .master.peak_rss_median)}] as $memory
| "## PR #\($pr) against master",
  "",
  (if $differs == [] then "- **Output** matches master on every workload"
   else "- **Output differs** from master", ($differs[] | "  - \(name(.))") end),
  (if $changed == [] then "- **Time** shows no significant change on \($pairs | length) workloads"
   else "- **Time** changed on \($changed | length) of \($pairs | length) workloads",
     ($changed[] | "  - **\(.verdict)** \(name(.scenario)): **\(1 / .speedup_median | f2)×** [\(1 / .speedup_median_ci[1] | f2), \(1 / .speedup_median_ci[0] | f2)]") end),
  (if $memory != [] then ($memory | max_by(.r)) as $top | "- **Peak memory** changes at most **\($top.r | f2)×**, on \(name($top.s))" else empty end),
  "",
  "Ratios are the pull request over master, with 95% intervals.",
  "",
  chart("Median time change against master in %"; [$pairs[].scenario];
    [{kind: "bar", name: "median", values: [$pairs[] | 1 / .speedup_median | percent]},
     {kind: "line", name: "95% CI high", values: [$pairs[] | 1 / .speedup_median_ci[0] | percent]},
     {kind: "line", name: "95% CI low", values: [$pairs[] | 1 / .speedup_median_ci[1] | percent]}]),
  "",
  (if $memory != [] then
    chart("Peak memory change against master in %"; [$memory[].s];
      [{kind: "bar", name: "peak RSS", values: [$memory[].r | percent]}]), ""
   else empty end)
