"""Optional plots of timing samples, coloured by measurement round."""

from collections.abc import Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Literal, Protocol

import numpy as np
import numpy.typing as npt

from bench.schema import Run

if TYPE_CHECKING:
    from matplotlib.axes import Axes
    from matplotlib.cm import ScalarMappable
    from matplotlib.colors import Normalize
    from matplotlib.figure import Figure

type FloatArray = npt.NDArray[np.float64]


class PlotAxes(Protocol):
    def boxplot(
        self,
        x: FloatArray,
        *,
        positions: Sequence[float],
        orientation: Literal["vertical", "horizontal"],
        widths: float,
        showfliers: bool,
        medianprops: dict[str, str],
    ) -> object: ...

    def scatter(
        self,
        x: FloatArray,
        y: FloatArray,
        *,
        c: npt.NDArray[np.int64],
        cmap: str,
        norm: Normalize,
        s: float,
        alpha: float,
        zorder: float,
    ) -> object: ...

    def set_yticks(self, ticks: Sequence[int]) -> object: ...

    def set_yticklabels(self, labels: Sequence[str]) -> object: ...

    def set_xlabel(self, xlabel: str) -> object: ...

    def set_title(self, label: str, *, fontsize: float) -> object: ...

    def grid(self, *, axis: Literal["both", "x", "y"], alpha: float) -> None: ...


class PlotFigure(Protocol):
    def colorbar(
        self,
        mappable: ScalarMappable,
        *,
        ax: Axes,
        label: str,
        fraction: float,
        ticks: Sequence[int],
    ) -> object: ...

    def tight_layout(self) -> None: ...

    def savefig(self, fname: Path, *, dpi: float) -> None: ...


def plot_axes(ax: Axes) -> PlotAxes:
    return ax


def plot_figure(fig: Figure) -> PlotFigure:
    return fig


def make_plots(results: Path, run: Run, names: list[str]) -> dict[str, str]:
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.cm import ScalarMappable
        from matplotlib.colors import Normalize
    except ImportError as error:
        raise ValueError("plots require uv sync --extra plots") from error
    (results / "plots").mkdir(exist_ok=True)
    out: dict[str, str] = {}
    for s, sc in run.scenarios.items():
        data = [(n, run.samples[s][n]) for n in names if run.samples[s][n].n]
        if not data:
            continue
        nrounds = max((r.round for _, e in data for r in e.rounds), default=1)
        norm = Normalize(vmin=1, vmax=nrounds)
        mpl_fig, mpl_ax = plt.subplots(figsize=(7, 1.2 + 0.9 * len(data)))
        fig, ax = plot_figure(mpl_fig), plot_axes(mpl_ax)
        ys: list[str] = []
        for i, (n, e) in enumerate(data):
            t = np.asarray(e.times, dtype=np.float64) * 1000
            _ = ax.boxplot(
                t,
                positions=[i],
                orientation="horizontal",
                widths=0.5,
                showfliers=False,
                medianprops={"color": "black"},
            )
            rounds = np.asarray(
                [r.round for r in e.rounds for _ in r.times], dtype=np.int64
            )
            jitter = (np.random.default_rng(i).random(len(t)) - 0.5) * 0.3
            _ = ax.scatter(
                t,
                i + jitter,
                c=rounds,
                cmap="viridis",
                norm=norm,
                s=12,
                alpha=0.7,
                zorder=3,
            )
            ys.append(n)
        _ = ax.set_yticks(range(len(ys)))
        _ = ax.set_yticklabels(ys)
        _ = ax.set_xlabel("wall time (ms); points coloured by round")
        _ = ax.set_title(f"{s}: {sc.description}", fontsize=10)
        ax.grid(axis="x", alpha=0.3)
        _ = fig.colorbar(
            ScalarMappable(norm=norm, cmap="viridis"),
            ax=mpl_ax,
            label="round",
            fraction=0.05,
            ticks=range(1, nrounds + 1),
        )
        fig.tight_layout()
        fig.savefig(results / "plots" / f"{s}.png", dpi=110)
        plt.close(mpl_fig)
        out[s] = f"plots/{s}.png"
    return out
