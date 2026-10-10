"""Compare ShellCheck implementations: prepare, measure, and report."""

import subprocess
import sys
from pathlib import Path

from bench import candidates, corpus, measure


class Args(measure.Args):
    omarchy: bool = False
    omarchy_source: Path | None = None


def main(argv: list[str] | None = None) -> None:
    arguments = list(sys.argv[1:] if argv is None else argv)
    try:
        if arguments and arguments[0] == "prepare":
            candidates.main(arguments[1:])
            return
        if arguments and arguments[0] == "run":
            measure.main(arguments[1:])
            return
        if arguments and arguments[0] == "report":
            from bench.analyze import main as report

            report(arguments[1:])
            return
        if arguments and arguments[0] == "corpus":
            corpus.main(arguments[1:])
            return
        parser = measure.parser()
        parser.description = __doc__
        parser.epilog = "Stages: bench prepare --help; bench run --help; bench report --help. The default command prepares, generates workloads, measures, and reports."
        # The default command shares run's flags and accepts preparation overrides.
        parser.add_argument("--state", type=Path, default=candidates.STATE)
        parser.add_argument(
            "--binary", action="append", default=[], metavar="NAME=PATH"
        )
        parser.add_argument(
            "--source", action="append", default=[], metavar="NAME=PATH"
        )
        parser.add_argument(
            "--omarchy", action="store_true", help="include pinned Omarchy workloads"
        )
        parser.add_argument("--omarchy-source", type=Path)
        args = parser.parse_args(arguments, namespace=Args())
        if args.omarchy_source and not args.omarchy:
            raise ValueError("--omarchy-source requires --omarchy")
        table = candidates.specs(args.config)
        plan = candidates.resolve(
            table,
            args.candidates,
            candidates.overrides(args.binary, table),
            candidates.overrides(args.source, table),
            args.state.resolve(),
        )
        candidates.prepare(plan, args.state.resolve(), args.prepared.resolve())
        if args.omarchy or not (args.corpus / "corpus.json").exists():
            corpus_arguments = ["--out", str(args.corpus)]
            if args.omarchy:
                corpus_arguments.append("--omarchy")
            if args.omarchy_source:
                corpus_arguments.extend(("--omarchy-source", str(args.omarchy_source)))
            corpus.main(corpus_arguments)
        run_flags = {
            action.dest: action.option_strings[0]
            for action in measure.parser()._actions
            if action.option_strings and action.dest != "help"
        }
        run_arguments: list[str] = []
        for name, flag in run_flags.items():
            value = getattr(args, name)
            if value is not None and value != "":
                run_arguments.extend((flag, str(value)))
        results = measure.main(run_arguments)
        from bench.analyze import RESAMPLES, analyze

        analyze(results, plots=False, resamples=RESAMPLES)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"bench: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
