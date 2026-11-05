"""Generate images of constructions for constants.

This is run on demand, not as part of the build, so that new images can be
reviewed before they're used:

    python scripts/generate_images.py                    # every family
    python scripts/generate_images.py ramsey cage        # some families
    python scripts/generate_images.py --sheet review.html

Images are written to assets/images/generated/, named by constant ID. To show
one on the site, point the constant's image to it in source_data/constants.yml:

    ramsey-4-4:
      image:
        generated: ramsey-4-4.svg
        alt_text: "..."

Each renderer checks its construction before drawing it: against a
certificate's witness where there is one, and otherwise against the
constant's value. The --sheet option also writes a self-contained HTML page
showing each generated image next to the image the constant uses now.

Images are SVG drawn in a shared style: the larger side is SIZE pixels, with
strokes and colors from the constants below.
"""

import argparse
import base64
import html
import itertools
import math
import os
import pathlib
from typing import Any, Callable, Iterable, Sequence

import yaml

from certificates import (eccentricity_at_most, girth, has_monochromatic_sum, is_cap, is_snake, load_certificates,
                          no_three_collinear, orbit_closure, read_grid_points, read_graph, read_marks, read_points, read_symmetries, read_ternary_points,
                          read_transitions, read_vectors, read_witness_data, transition_vertices)
from utils import GENERATED_IMAGES_DIR

#########
# Style #
#########

SIZE = 300                 # pixels on the larger side
PAD = 6                    # pixels of margin
INK = "#343a40"            # outlines, text and containers
MUTED = "#ced4da"          # background cells and guides
FILL = "#dbe7f5"           # shapes being packed
EDGE = "#3a6ea5"           # their outlines, graph edges
FONT = "system-ui, -apple-system, 'Segoe UI', Roboto, sans-serif"
# Categorical colors, for colorings and states
PALETTE = ["#3a6ea5", "#e07b39", "#4a9a5b", "#b0457a", "#d4a72c", "#2a9d8f"]


def num(x: float) -> str:
    """A pixel coordinate, to 0.1 px."""
    s = f"{x:.1f}".rstrip("0").rstrip(".")
    return "0" if s == "-0" else s


def attrs(**kwargs: Any) -> str:
    """SVG attributes, with `_` in names written as `-` and floats rounded."""
    return "".join(
        f' {k.rstrip("_").replace("_", "-")}="{num(v) if isinstance(v, float) else v}"'
        for k, v in kwargs.items() if v is not None
    )


class Svg:
    """An SVG drawing in math coordinates (y up) of the box [xmin, xmax] ×
    [ymin, ymax], scaled so that its larger side is `size` pixels.

    Drawing methods return element strings, so elements can be grouped with
    `group` to share attributes; `add` puts them in the drawing.
    """

    def __init__(self, xmin: float, ymin: float, xmax: float, ymax: float, size: float = SIZE, pad: float = PAD) -> None:
        self.scale = size / max(xmax - xmin, ymax - ymin)
        self.xmin, self.ymax, self.pad = xmin, ymax, pad
        self.width = (xmax - xmin) * self.scale + 2 * pad
        self.height = (ymax - ymin) * self.scale + 2 * pad
        self.defs: list[str] = []
        self.elements: list[str] = []

    def x(self, x: float) -> float:
        return (x - self.xmin) * self.scale + self.pad

    def y(self, y: float) -> float:
        return (self.ymax - y) * self.scale + self.pad

    def points(self, pts: Iterable[Sequence[float]]) -> str:
        return " ".join(f"{num(self.x(p[0]))},{num(self.y(p[1]))}" for p in pts)

    def add(self, *elements: str) -> None:
        self.elements.extend(elements)

    def group(self, elements: Iterable[str], **kwargs: Any) -> str:
        return f"<g{attrs(**kwargs)}>{''.join(elements)}</g>"

    def line(self, p: Sequence[float], q: Sequence[float], **kwargs: Any) -> str:
        return f"<line{attrs(x1=self.x(p[0]), y1=self.y(p[1]), x2=self.x(q[0]), y2=self.y(q[1]), **kwargs)}/>"

    def polyline(self, pts: Iterable[Sequence[float]], **kwargs: Any) -> str:
        return f'<polyline points="{self.points(pts)}"{attrs(**kwargs)}/>'

    def polygon(self, pts: Iterable[Sequence[float]], **kwargs: Any) -> str:
        return f'<polygon points="{self.points(pts)}"{attrs(**kwargs)}/>'

    def circle(self, c: Sequence[float], r: float, **kwargs: Any) -> str:
        return f"<circle{attrs(cx=self.x(c[0]), cy=self.y(c[1]), r=r * self.scale, **kwargs)}/>"

    def rect(self, x: float, y: float, w: float, h: float, **kwargs: Any) -> str:
        """The rectangle [x, x + w] × [y, y + h]."""
        return f"<rect{attrs(x=self.x(x), y=self.y(y + h), width=w * self.scale, height=h * self.scale, **kwargs)}/>"

    def path(self, d: str, **kwargs: Any) -> str:
        return f'<path d="{d}"{attrs(**kwargs)}/>'

    def text(self, p: Sequence[float], s: Any, size: float, **kwargs: Any) -> str:
        """Text centered at p, `size` units high."""
        return (f"<text{attrs(x=self.x(p[0]), y=self.y(p[1]), font_size=size * self.scale, text_anchor='middle', dominant_baseline='central', **kwargs)}>"
                f"{html.escape(str(s))}</text>")

    def render(self) -> str:
        w, h = num(self.width), num(self.height)
        defs = f"<defs>{''.join(self.defs)}</defs>" if self.defs else ""
        return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}">'
                f"{defs}{''.join(self.elements)}</svg>\n")


#########
# Data #
#########

_certificates: dict[str, dict[str, Any]] | None = None
_constants: dict[str, Any] | None = None


def certificates() -> dict[str, dict[str, Any]]:
    global _certificates
    if _certificates is None:
        _certificates = load_certificates()
    return _certificates


def witness(constant_id: str, bound: str) -> dict[str, Any] | None:
    """The strongest witness certificate for a bound on a constant, if any."""
    certs = [c for c in certificates().values()
             if c["constant"] == constant_id and c["bound"] == bound and c["kind"] == "witness"]
    if not certs:
        return None
    return (max if bound == "lower" else min)(certs, key=lambda c: c["approx"])


def exact_value(constant_id: str) -> float | None:
    """A constant's exact value, if known, from _data/constants.yml (written
    by scripts/process_data.py)."""
    global _constants
    if _constants is None:
        with open("_data/constants.yml") as file:
            _constants = yaml.safe_load(file)
    value = _constants[constant_id].get("exact_value")
    return None if value is None else float(value["decimal_approx"])


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def adjacency(n: int, edges: Iterable[tuple[int, int]]) -> list[int]:
    """Bitmask adjacency lists, as used by scripts/certificates.py."""
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def edge_list(adj: list[int]) -> list[tuple[int, int]]:
    return [(u, v) for u in range(len(adj)) for v in range(u + 1, len(adj)) if adj[u] >> v & 1]


def on_circle(n: int, r: float = 1, start: float = 90) -> list[tuple[float, float]]:
    """n points evenly spaced counterclockwise on a circle, the first at
    angle `start` degrees."""
    return [(r * math.cos(math.radians(start + 360 * i / n)), r * math.sin(math.radians(start + 360 * i / n)))
            for i in range(n)]


##########
# Graphs #
##########

def draw_graph(pos: Sequence[tuple[float, float]], edges: Iterable[tuple[int, int]],
               edge_width: float = 1.5, vertex_radius: float = 4) -> Svg:
    """A graph drawing with vertices at pos (in a box about [-1, 1]²)."""
    m = 1.08
    svg = Svg(-m, -m, m, m)
    svg.add(svg.group((svg.line(pos[u], pos[v]) for u, v in edges),
                      stroke=EDGE, stroke_width=edge_width, stroke_linecap="round"))
    svg.add(svg.group((svg.circle(p, vertex_radius / svg.scale) for p in pos),
                      fill=INK, stroke="white", stroke_width=1))
    return svg


def lcf(n: int, jumps: Sequence[int]) -> list[tuple[int, int]]:
    """Edges of the cubic graph with LCF notation [jumps]^(n / len(jumps)):
    a Hamiltonian cycle plus a chord from each vertex i to i + jumps[i]."""
    edges = {(i, (i + 1) % n) for i in range(n)}
    for i in range(n):
        j = (i + jumps[i % len(jumps)]) % n
        edges.add((min(i, j), max(i, j)))
    return sorted(edges)


def petersen() -> tuple[list[tuple[float, float]], list[tuple[int, int]]]:
    """The Petersen graph: an outer pentagon, spokes and an inner pentagram."""
    pos = on_circle(5) + on_circle(5, 0.5)
    edges = ([(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
             + [(5 + i, 5 + (i + 2) % 5) for i in range(5)])
    return pos, edges


def cage_graph(k: int, g: int) -> tuple[list[tuple[float, float]], list[tuple[int, int]]] | None:
    """A drawing of the (k, g)-cage, for the cages drawn so far."""
    if g in (3, 4) and k > 7:  # denser drawings are a blur
        return None
    if g == 3:  # complete graph
        n = k + 1
        return on_circle(n), [(u, v) for u in range(n) for v in range(u + 1, n)]
    if g == 4:  # complete bipartite graph, in two columns
        pos = [(-0.6, 1 - 2 * i / (k - 1)) for i in range(k)] + [(0.6, 1 - 2 * i / (k - 1)) for i in range(k)]
        return pos, [(u, k + v) for u in range(k) for v in range(k)]
    if (k, g) == (3, 5):
        return petersen()
    lcfs = {6: (14, [5, -5]), 7: (24, [12, 7, -7]), 8: (30, [-13, -9, 7, -7, 9, 13])}
    if k == 3 and g in lcfs:
        n, jumps = lcfs[g]
        return on_circle(n), lcf(n, jumps)
    return None


def render_cage(constant_id: str, k: int, g: int) -> Svg | None:
    graph = cage_graph(k, g)
    if graph is None:
        return None
    pos, edges = graph
    adj = adjacency(len(pos), edges)
    check(all(bin(a).count("1") == k for a in adj), f"{constant_id}: not {k}-regular")
    check(girth(adj) == g, f"{constant_id}: girth is not {g}")
    check(len(pos) == exact_value(constant_id), f"{constant_id}: {len(pos)} vertices is not the cage's order")
    small = len(pos) <= 10
    return draw_graph(pos, edges, edge_width=2 if small else 1.5, vertex_radius=5 if small else 3.5)


def render_degree_diameter(constant_id: str, d: int, k: int) -> Svg | None:
    if (d, k) != (3, 2):
        return None
    pos, edges = petersen()
    adj = adjacency(len(pos), edges)
    check(max(bin(a).count("1") for a in adj) <= d, f"{constant_id}: degree above {d}")
    check(all(eccentricity_at_most(adj, v, k) for v in range(len(adj))), f"{constant_id}: diameter above {k}")
    check(len(pos) == exact_value(constant_id), f"{constant_id}: {len(pos)} vertices is not the value")
    return draw_graph(pos, edges, edge_width=2, vertex_radius=5)


def render_ramsey(constant_id: str, r: int, s: int) -> Svg | None:
    """A two-coloring of the edges of a complete graph with no monochromatic
    K_r in the first color (edges of the witness graph) or K_s in the second
    (non-edges), drawn with the vertices on a circle."""
    if (r, s) == (3, 3):  # the 5-cycle and its complement
        adj = adjacency(5, [(i, (i + 1) % 5) for i in range(5)])
    else:
        cert = witness(constant_id, "lower")
        if cert is None:
            return None
        adj = read_graph(cert)
        if len(adj) > 20:  # denser drawings are a blur
            return None
    n = len(adj)
    pos = on_circle(n)
    pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    first = [(u, v) for u, v in pairs if adj[u] >> v & 1]
    second = [(u, v) for u, v in pairs if not adj[u] >> v & 1]
    width = 2 if n <= 10 else 1 if n <= 20 else 0.5
    m = 1.08
    svg = Svg(-m, -m, m, m)
    svg.add(svg.group((svg.line(pos[u], pos[v]) for u, v in second), stroke=PALETTE[1], stroke_width=width))
    svg.add(svg.group((svg.line(pos[u], pos[v]) for u, v in first), stroke=PALETTE[0], stroke_width=width))
    radius = 5 if n <= 10 else 3.5 if n <= 20 else 2.5
    svg.add(svg.group((svg.circle(p, radius / svg.scale) for p in pos), fill=INK, stroke="white", stroke_width=1))
    return svg


#############
# Colorings #
#############

def render_van_der_waerden(constant_id: str, r: int, k: int) -> Svg | None:
    """A coloring of 1, ..., W - 1 with no monochromatic k-term arithmetic
    progression, as rows of colored cells."""
    cert = witness(constant_id, "lower")
    if cert is None:
        return None
    colors = "".join(read_witness_data(cert).split())
    return draw_coloring(colors)


def render_schur(constant_id: str, k: int, weak: bool) -> Svg | None:
    """A coloring of 1, ..., S(k) (or WS(k)) with no monochromatic solution
    to x + y = z (with x ≠ y for WS), as rows of colored cells."""
    cert = witness(constant_id, "lower")
    if cert is None or k < 2:
        return None
    colors = "".join(read_witness_data(cert).split())
    check(not has_monochromatic_sum(colors, weak), f"{constant_id}: coloring has a monochromatic sum")
    return draw_coloring(colors)


def draw_coloring(colors: str) -> Svg | None:
    """A coloring of 1, ..., n (one digit per integer) as rows of colored
    cells, numbered if there are only a few."""
    n = len(colors)
    if n > 300:
        return None
    per_row = n if n <= 40 else math.ceil(math.sqrt(n * 4))
    rows = math.ceil(n / per_row)
    gap = 0.12
    svg = Svg(0, -0.6 if n <= 12 else 0, per_row, rows, size=max(SIZE, min(600, 30 * per_row)))
    cells: dict[str, list[str]] = {}
    for i, c in enumerate(colors):
        x, y = i % per_row, rows - 1 - i // per_row
        cells.setdefault(c, []).append(svg.rect(x + gap / 2, y + gap / 2, 1 - gap, 1 - gap))
    for c in sorted(cells):
        svg.add(svg.group(cells[c], fill=PALETTE[int(c)]))
    if n <= 12:
        svg.add(svg.group((svg.text((i + 0.5, -0.3), i + 1, 0.4) for i in range(n)), fill=INK, font_family=FONT))
    return svg


############
# Packings #
############

def render_circle_in_equilateral(constant_id: str, n: int) -> Svg | None:
    """The witness packing of n unit circles in an equilateral triangle."""
    cert = witness(constant_id, "upper")
    if cert is None:
        return None
    s = cert["approx"]
    centers = [(float(x), float(y)) for x, y in read_points(read_witness_data(cert))]
    h = s * math.sqrt(3) / 2
    svg = Svg(0, 0, s, h)
    svg.add(svg.group((svg.circle(c, 1) for c in centers), fill=FILL, stroke=EDGE, stroke_width=1.5))
    svg.add(svg.polygon([(0, 0), (s, 0), (s / 2, h)], fill="none", stroke=INK, stroke_width=2, stroke_linejoin="round"))
    return svg


Square = tuple[float, float, float]  # center x, center y, angle in degrees


def square_corners(sq: Square) -> list[tuple[float, float]]:
    cx, cy, angle = sq
    t = math.radians(angle)
    return [(cx + (dx * math.cos(t) - dy * math.sin(t)) / 2, cy + (dx * math.sin(t) + dy * math.cos(t)) / 2)
            for dx, dy in [(-1, -1), (1, -1), (1, 1), (-1, 1)]]


def overlap(a: list[tuple[float, float]], b: list[tuple[float, float]], eps: float = 1e-9) -> bool:
    """Whether two convex polygons have overlapping interiors (separating
    axis test)."""
    for poly in (a, b):
        for (x1, y1), (x2, y2) in zip(poly, poly[1:] + poly[:1]):
            nx, ny = y2 - y1, x1 - x2
            pa = [nx * x + ny * y for x, y in a]
            pb = [nx * x + ny * y for x, y in b]
            if max(pa) <= min(pb) + eps or max(pb) <= min(pa) + eps:
                return False
    return True


def square_packing(n: int) -> tuple[float, list[Square]]:
    """A packing of n unit squares in the smallest square, for the cases
    drawn so far: side ⌈√n⌉ when that's optimal, in a grid, and n = 5."""
    if n == 5:
        s = 2 + 1 / math.sqrt(2)
        return s, [(0.5, 0.5, 0), (s - 0.5, 0.5, 0), (0.5, s - 0.5, 0), (s - 0.5, s - 0.5, 0), (s / 2, s / 2, 45)]
    k = math.ceil(math.sqrt(n))
    return k, [(i % k + 0.5, k - 1 - i // k + 0.5, 0) for i in range(n)]


def render_square_packing(constant_id: str, n: int) -> Svg | None:
    s, squares = square_packing(n)
    value = exact_value(constant_id)
    if value is None or abs(s - value) > 1e-6:
        return None
    corners = [square_corners(sq) for sq in squares]
    check(all(-1e-9 <= c <= s + 1e-9 for poly in corners for p in poly for c in p), f"{constant_id}: square outside container")
    check(not any(overlap(a, b) for a, b in itertools.combinations(corners, 2)), f"{constant_id}: squares overlap")
    svg = Svg(0, 0, s, s)
    width = 1.5 if s <= 5 else 1
    svg.add(svg.group((svg.polygon(poly) for poly in corners), fill=FILL, stroke=EDGE, stroke_width=width, stroke_linejoin="round"))
    svg.add(svg.rect(0, 0, s, s, fill="none", stroke=INK, stroke_width=2))
    return svg


def render_kissing_number(constant_id: str, n: int) -> Svg | None:
    """Unit spheres touching a central one: in dimensions 1 and 2 as circles,
    in dimension 3 as shaded balls in perspective-free projection."""
    cert = witness(constant_id, "lower")
    if cert is None or n > 3:
        return None
    vectors = read_vectors(read_witness_data(cert))
    if "symmetries" in cert["witness"]:
        vectors = orbit_closure(vectors, read_symmetries(cert["witness"]["symmetries"], len(vectors[0])), 1000)
    check(len(vectors) == exact_value(constant_id), f"{constant_id}: witness isn't optimal")
    # Coordinates in an orthonormal basis of their span, padded to 3D
    basis: list[list[float]] = []
    for v in vectors:
        w = [float(x) for x in v]
        for b in basis:
            dot = sum(x * y for x, y in zip(w, b))
            w = [x - dot * y for x, y in zip(w, b)]
        norm = math.sqrt(sum(x * x for x in w))
        if norm > 1e-9:
            basis.append([x / norm for x in w])
    centers = []
    for v in vectors:
        coords = [sum(x * y for x, y in zip(v, b)) for b in basis] + [0] * (3 - len(basis))
        norm = math.sqrt(sum(x * x for x in coords))
        centers.append([2 * x / norm for x in coords])
    if n == 1:
        centers = [(x, 0, 0) for x, _, _ in centers]
    if n <= 2:
        m = 3.02
        svg = Svg(-m, -1.02 if n == 1 else -m, m, 1.02 if n == 1 else m)
        svg.add(svg.circle((0, 0), 1, fill=PALETTE[1], fill_opacity=0.35, stroke=PALETTE[1], stroke_width=1.5))
        svg.add(svg.group((svg.circle(c[:2], 1) for c in centers), fill=FILL, stroke=EDGE, stroke_width=1.5))
        return svg
    # Rotate for a view that shows the structure, then draw back to front
    def rotate(p: Sequence[float], axis: int, degrees: float) -> list[float]:
        t = math.radians(degrees)
        i, j = [a for a in range(3) if a != axis]
        q = list(p)
        q[i], q[j] = p[i] * math.cos(t) - p[j] * math.sin(t), p[i] * math.sin(t) + p[j] * math.cos(t)
        return q
    balls = [(rotate(rotate(c, 2, 20), 0, -25), "outer") for c in centers] + [([0, 0, 0], "center")]
    balls.sort(key=lambda b: -b[0][1])  # y is depth: larger is farther
    m = 3.02
    svg = Svg(-m, -m, m, m)
    for name, light, color in [("outer", FILL, "#7f9fc6"), ("center", "#f6dcc8", PALETTE[1])]:
        svg.defs.append(f'<radialGradient id="{name}" cx="0.35" cy="0.3" r="0.75">'
                        f'<stop offset="0" stop-color="white"/><stop offset="0.45" stop-color="{light}"/>'
                        f'<stop offset="1" stop-color="{color}"/></radialGradient>')
    svg.add(svg.group((svg.circle((p[0], p[2]), 1, fill=f"url(#{name})") for p, name in balls),
                      stroke=INK, stroke_width=0.75, stroke_opacity=0.6, fill_opacity=0.9))
    return svg


##########
# Strings #
##########

def render_superpermutation(constant_id: str, n: int) -> Svg | None:
    """A shortest known superpermutation, with brackets under each
    permutation it contains."""
    cert = witness(constant_id, "upper")
    if cert is None or n < 2 or n > 4:
        return None
    s = "".join(read_witness_data(cert).split())
    starts = [i for i in range(len(s) - n + 1) if sorted(s[i:i + n]) == [str(d) for d in range(1, n + 1)]]
    check(len({s[i:i + n] for i in starts}) == math.factorial(n), f"{constant_id}: missing permutations")
    check(len(s) == exact_value(constant_id), f"{constant_id}: witness isn't optimal")
    lanes: list[int] = []  # end of the last bracket in each lane
    brackets = []
    for i in starts:
        lane = next((j for j, end in enumerate(lanes) if end <= i), len(lanes))
        if lane == len(lanes):
            lanes.append(0)
        lanes[lane] = i + n
        brackets.append((i, lane))
    depth = 0.3 + 0.35 * len(lanes)
    svg = Svg(0, -depth, len(s), 1.1, size=max(SIZE, min(640, 22 * len(s))))
    svg.add(svg.group((svg.rect(i + 0.05, 0.05, 0.9, 0.9, fill=PALETTE[int(c) - 1], fill_opacity=0.25) for i, c in enumerate(s))))
    svg.add(svg.group((svg.text((i + 0.5, 0.5), c, 0.6) for i, c in enumerate(s)), fill=INK, font_family=FONT))
    svg.add(svg.group((svg.polyline([(i + 0.15, -0.2 - 0.35 * lane + 0.12), (i + 0.15, -0.2 - 0.35 * lane),
                                      (i + n - 0.15, -0.2 - 0.35 * lane), (i + n - 0.15, -0.2 - 0.35 * lane + 0.12)])
                       for i, lane in brackets), fill="none", stroke=EDGE, stroke_width=1.5))
    return svg


##########
# Rulers #
##########

def render_golomb_ruler(constant_id: str, n: int) -> Svg | None:
    """The shortest known Golomb ruler with n marks. For a few marks, each
    distance between two marks is drawn below the ruler, shortest first, to
    show that they're all different."""
    cert = witness(constant_id, "upper")
    if cert is None or n < 2:
        return None
    marks = sorted(read_marks(read_witness_data(cert)))
    pairs = sorted(itertools.combinations(marks, 2), key=lambda p: p[1] - p[0])
    check(len({b - a for a, b in pairs}) == len(pairs), f"{constant_id}: distances repeat")
    length = marks[-1] - marks[0]
    if exact_value(constant_id) is not None:
        check(length == exact_value(constant_id), f"{constant_id}: ruler isn't optimal")
    rows = pairs if n <= 6 else []
    u = length / (10 if rows else 16)  # height of the ruler, in the ruler's units
    depth = 0.7 * u * len(rows)
    label = 0.6 * u if rows else 0
    svg = Svg(-u, -depth - 0.4 * u, length + (1.6 if rows else 1) * u, u + 1.4 * label + 0.2 * u, size=max(SIZE, min(600, 40 * n)))
    svg.add(svg.rect(marks[0], 0, length, u, fill=FILL, stroke=INK, stroke_width=1))
    svg.add(svg.group((svg.line((a, 0), (a, u)) for a in marks), stroke=INK, stroke_width=2))
    if label:
        svg.add(svg.group((svg.text((a, u + 0.75 * label), a, label) for a in marks), fill=INK, font_family=FONT))
    for i, (a, b) in enumerate(rows):
        y = -0.7 * u * (i + 1)
        svg.add(svg.line((a, y), (b, y), stroke=EDGE, stroke_width=2),
                svg.group((svg.circle((x, y), 0.1 * u) for x in (a, b)), fill=EDGE),
                svg.text((b + 0.8 * u, y), b - a, 0.55 * u, fill=INK, font_family=FONT))
    return svg


##############
# Hypercubes #
##############

# Projections of Q_n to the plane, as the image of each unit vector: a small
# cube for the first three coordinates, offset along longer vectors for the
# others, chosen by a random search so that no vertex is close to an edge it
# isn't on.
HYPERCUBE_PROJECTIONS = {
    2: [(1, 0), (0, 1)],
    3: [(1, 0), (0, 1), (0.42, 0.3)],
    4: [(1, 0), (0, 1), (0.42, 0.3), (-0.43, 1.79)],
    5: [(1, 0), (0, 1), (0.42, 0.3), (-0.47, 1.97), (1.93, 0.65)],
}


def render_snake(constant_id: str, n: int, coil: bool) -> Svg | None:
    """The longest known snake (or coil) in Q_n, drawn over a projection of
    the hypercube."""
    cert = witness(constant_id, "lower")
    if cert is None or n < 2 or n not in HYPERCUBE_PROJECTIONS:
        return None
    transitions = read_transitions(read_witness_data(cert), n)
    check(is_snake(transitions, n, coil), f"{constant_id}: not an induced {'cycle' if coil else 'path'}")
    if exact_value(constant_id) is not None:
        check(len(transitions) == exact_value(constant_id), f"{constant_id}: witness isn't optimal")
    vectors = HYPERCUBE_PROJECTIONS[n]
    pos = [(sum(vectors[i][0] for i in range(n) if v >> i & 1), sum(vectors[i][1] for i in range(n) if v >> i & 1))
           for v in range(1 << n)]
    xs, ys = [p[0] for p in pos], [p[1] for p in pos]
    m = 0.15
    svg = Svg(min(xs) - m, min(ys) - m, max(xs) + m, max(ys) + m, size=SIZE if n <= 4 else 400)
    px = 1 / svg.scale  # one pixel, in drawing units
    svg.add(svg.group((svg.line(pos[v], pos[v ^ 1 << i]) for v in range(1 << n) for i in range(n) if not v >> i & 1),
                      stroke=MUTED, stroke_width=1.25 if n <= 4 else 1))
    vertices = transition_vertices(transitions)
    path = [pos[v] for v in vertices]
    style = dict(fill="none", stroke=EDGE, stroke_width=4 if n <= 4 else 3, stroke_linecap="round", stroke_linejoin="round")
    svg.add(svg.polygon(path[:-1], **style) if coil else svg.polyline(path, **style))
    on_path = set(vertices)
    radius = (3 if n <= 4 else 2) * px
    svg.add(svg.group((svg.circle(pos[v], radius) for v in range(1 << n) if v not in on_path), fill="#adb5bd"))
    svg.add(svg.group((svg.circle(pos[v], radius * 1.4) for v in on_path), fill=INK, stroke="white", stroke_width=1))
    if not coil:
        svg.add(svg.group((svg.circle(path[i], radius * 2) for i in (0, -1)), fill=PALETTE[1], stroke="white", stroke_width=1))
    return svg


def stamp_foldings(n: int) -> list[tuple[int, ...]]:
    """All foldings of a strip of n stamps, as the position of each stamp in
    the folded stack. The crease after stamp i is on the right for even i and
    the left for odd i, and creases on the same side can't cross."""
    foldings = []
    for pos in itertools.permutations(range(n)):
        ok = True
        for side in (0, 1):
            creases = [sorted((pos[i], pos[i + 1])) for i in range(side, n - 1, 2)]
            if any(a < c < b < d or c < a < d < b for (a, b), (c, d) in itertools.combinations(creases, 2)):
                ok = False
                break
        if ok:
            foldings.append(pos)
    return foldings


def draw_folding(svg: Svg, pos: Sequence[int], x0: float, y0: float, label: bool) -> list[str]:
    """The folded strip as one path, stamps 2 units long and stacked 1 apart,
    with its bottom left at (x0, y0)."""
    n = len(pos)
    elements = []
    d = ""
    for i in range(n):
        y = y0 + pos[i]
        left, right = (x0, x0 + 2) if i % 2 == 0 else (x0 + 2, x0)
        if i == 0:
            d += f"M{num(svg.x(left))} {num(svg.y(y))}"
        else:
            # Arc from the end of the previous stamp, bulging outward
            r = abs(y - (y0 + pos[i - 1])) / 2 * svg.scale
            going_up = y > y0 + pos[i - 1]
            sweep = int(not going_up) if i % 2 == 1 else int(going_up)
            d += f"A{num(r)} {num(r)} 0 0 {sweep} {num(svg.x(left))} {num(svg.y(y))}"
        d += f"L{num(svg.x(right))} {num(svg.y(y))}"
        if label:
            elements.append(svg.text((x0 + 1, y + 0.32), i + 1, 0.42))
    return [svg.path(d, fill="none", stroke=EDGE, stroke_width=3, stroke_linecap="round", stroke_linejoin="round"),
            svg.group(elements, fill=INK, font_family=FONT)]


def render_stamp_folding(constant_id: str, n: int) -> Svg | None:
    """All foldings of n stamps for small n, or one of them."""
    if n > 8:
        return None
    foldings = stamp_foldings(n)
    check(len(foldings) == exact_value(constant_id), f"{constant_id}: {len(foldings)} foldings")
    if n > 4:
        foldings = [foldings[len(foldings) // 2]]
    cols = math.ceil(math.sqrt(len(foldings)))
    rows = math.ceil(len(foldings) / cols)
    margin = (n - 1) / 2 + 0.6  # room for arcs on either side
    cell_w, cell_h = 2 + 2 * margin, n + 0.2
    w, h = cols * cell_w, rows * cell_h
    svg = Svg(0, 0, w, h, size=min(SIZE, 40 * max(w, h)))  # at most 40 px per unit, so few stamps aren't huge
    for k, pos in enumerate(foldings):
        x0 = (k % cols) * cell_w + margin
        y0 = (rows - 1 - k // cols) * cell_h + 0.4
        svg.add(*draw_folding(svg, pos, x0, y0, label=len(foldings) == 1 or n <= 3))
    return svg


###################
# Turing machines #
###################

# Champion machines in standard text format: for each state, the actions on
# reading 0 and 1 (write, move, next state; Z halts)
BUSY_BEAVERS = {
    "shift": {1: "1RZ---", 2: "1RB1LB_1LA1RZ", 3: "1RB1RZ_1LB0RC_1LC1LA", 4: "1RB1LB_1LA0LC_1RZ1LD_1RD0RA"},
    "ones": {1: "1RZ---", 2: "1RB1LB_1LA1RZ", 3: "1RB1RZ_0RC1RB_1LC1LA", 4: "1RB1LB_1LA0LC_1RZ1LD_1RD0RA"},
}


def run_machine(machine: str, limit: int = 10_000) -> list[tuple[dict[int, int], int, int]]:
    """Run a machine on a blank tape: the tape, head and state before each
    step, and after the last (state -1 when halted)."""
    rules = [machine[i:i + 6] for i in range(0, len(machine), 7)]
    tape: dict[int, int] = {}
    head, state = 0, 0
    history = []
    for _ in range(limit):
        history.append((dict(tape), head, state))
        if state < 0:
            return history
        action = rules[state][3 * tape.get(head, 0):][:3]
        tape[head] = int(action[0])
        head += 1 if action[1] == "R" else -1
        state = -1 if action[2] == "Z" else ord(action[2]) - ord("A")
    raise ValueError(f"{machine} didn't halt in {limit} steps")


def rule_table(svg: Svg, machine: str, x0: float, y0: float, px: float) -> list[str]:
    """A machine's rules as a table with its top left at (x0, y0): a row per
    state and a column per symbol read, each entry the symbol written, the
    move and the next state (H to halt). `px` is the size of a pixel in
    drawing units."""
    rules = machine.split("_")
    row, label_w, action_w = 24 * px, 26 * px, 40 * px
    font = dict(font_size=13, text_anchor="middle", dominant_baseline="central")
    elements = []
    for j in range(2):
        elements.append(svg.text((x0 + label_w + (j + 0.5) * action_w, y0 - row / 2), j, 13 * px, fill="#6c757d"))
    for i, rule in enumerate(rules):
        y = y0 - (i + 1.5) * row
        elements.append(svg.line((x0, y + row / 2), (x0 + label_w + 2 * action_w, y + row / 2), stroke=MUTED, stroke_width=1))
        elements.append(svg.circle((x0 + label_w / 2, y), 9 * px, fill=PALETTE[i]))
        elements.append(svg.text((x0 + label_w / 2, y), chr(ord("A") + i), 12 * px, fill="white", font_weight="bold"))
        for j in range(2):
            action = rule[3 * j:3 * j + 3]
            x = svg.x(x0 + label_w + (j + 0.5) * action_w)
            if action == "---":
                elements.append(f"<text{attrs(x=x, y=svg.y(y), fill=MUTED, **font)}>–</text>")
                continue
            arrow = "→" if action[1] == "R" else "←"
            halt = action[2] == "Z"
            color = INK if halt else PALETTE[ord(action[2]) - ord("A")]
            elements.append(f"<text{attrs(x=x, y=svg.y(y), fill=INK, **font)}>{action[0]}{arrow}"
                            f"<tspan{attrs(fill=color, font_weight='bold')}>{'H' if halt else action[2]}</tspan></text>")
    return [svg.group(elements, font_family=FONT)]


def render_busy_beaver(constant_id: str, kind: str, n: int) -> Svg | None:
    """A champion machine's rule table, and its space-time diagram: time runs
    left to right and the tape top to bottom, with cells holding 1 shaded and
    the head at each step marked in its state's color (white once halted)."""
    machine = BUSY_BEAVERS[kind].get(n)
    if machine is None:
        return None
    history = run_machine(machine)
    steps = len(history) - 1
    ones = sum(history[-1][0].values())
    check((steps if kind == "shift" else ones) == exact_value(constant_id), f"{constant_id}: {steps} steps, {ones} ones")
    cells = sorted({p for tape, head, _ in history for p in [*tape, head]})
    lo, hi = cells[0], cells[-1]
    height = hi - lo + 1
    # Narrow the time steps of long runs so the diagram isn't too wide
    dt = max(0.4, min(1, 3 * height / len(history)))
    width = len(history) * dt
    # Size the diagram in pixels per tape cell, and the table in pixels
    px = 1 / min(24, 520 / max(width, height))
    table_w, table_h, gap = 106 * px, (n + 1) * 24 * px, 20 * px
    total_h = max(height, table_h)
    xmin = -(table_w + gap)
    svg = Svg(xmin, 0, width, total_h, size=max(width - xmin, total_h) / px)
    oy = (total_h - height) / 2  # bottom of the diagram
    svg.add(*rule_table(svg, machine, xmin, (total_h + table_h) / 2, px))
    svg.add(svg.rect(0, oy, width, height, fill="#f1f3f5"))
    # Each cell's 1s, merged over consecutive steps
    ones_cells = []
    for p in range(lo, hi + 1):
        bits = [tape.get(p, 0) for tape, _, _ in history] + [0]
        start = None
        for t, bit in enumerate(bits):
            if bit and start is None:
                start = t
            elif not bit and start is not None:
                ones_cells.append(svg.rect(start * dt, oy + hi - p + 0.06, (t - start) * dt, 0.88))
                start = None
    svg.add(svg.group(ones_cells, fill="#9fb4cc"))
    heads: dict[int, list[str]] = {s: [] for s in range(-1, n)}
    for t, (_, head, state) in enumerate(history):
        heads[state].append(svg.circle(((t + 0.5) * dt, oy + hi - head + 0.5), min(0.3, 0.45 * dt)))
    for state, marks in heads.items():
        if marks:
            svg.add(svg.group(marks, fill=PALETTE[state] if state >= 0 else "white", stroke=INK if state < 0 else None,
                              stroke_width=0.75 if state < 0 else None))
    return svg


############
# Cap sets #
############

def render_cap_set(constant_id: str, n: int) -> Svg | None:
    """The largest known cap set in F_3^n, drawn as in the card game SET: the
    points of F_3^n are cells of a grid, nested 3 by 3 blocks, with even
    coordinates across and odd coordinates up, from the innermost blocks out.
    Gaps between blocks widen with their level, so lines show as rows,
    columns and diagonals of blocks."""
    cert = witness(constant_id, "lower")
    if cert is None or n > 6:
        return None
    points = read_ternary_points(read_witness_data(cert), n)
    check(is_cap(points), f"{constant_id}: three points are on a line")
    if exact_value(constant_id) is not None:
        check(len(points) == exact_value(constant_id), f"{constant_id}: witness isn't optimal")
    gap = [0.0, 0.35, 0.8, 1.6]  # between blocks at each level, in cells

    def coord(digits: Sequence[int]) -> float:
        x, size = 0.0, 1.0  # size of a block at this level, with its gaps
        for level, d in enumerate(digits):
            x += d * (size + gap[level + 1])
            size = 3 * size + 2 * gap[level + 1]
        return x

    cols, rows = (n + 1) // 2, n // 2
    width = coord([2] * cols) + 1
    height = coord([2] * rows) + 1 if rows else 1
    svg = Svg(0, 0, width, height, size=SIZE if n <= 4 else 400)
    cap = set(points)
    cells, dots = [], []
    for p in itertools.product(range(3), repeat=n):
        x, y = coord(p[0::2]), coord(p[1::2])
        cells.append(svg.rect(x + 0.06, y + 0.06, 0.88, 0.88))
        if p in cap:
            dots.append(svg.circle((x + 0.5, y + 0.5), 0.36))
    svg.add(svg.group(cells, fill=MUTED, rx=1.5 if n >= 5 else 3))
    svg.add(svg.group(dots, fill=EDGE))
    return svg


####################
# No-three-in-line #
####################

def render_no_three_in_line(constant_id: str, n: int) -> Svg | None:
    """The points of a no-three-in-line configuration, drawn on the n x n
    grid."""
    cert = witness(constant_id, "lower")
    if cert is None or n < 2:
        return None
    points = read_grid_points(read_witness_data(cert))
    check(no_three_collinear(points), f"{constant_id}: three points are on a line")
    if exact_value(constant_id) is not None:
        check(len(points) == exact_value(constant_id), f"{constant_id}: witness isn't optimal")
    m = 0.5
    svg = Svg(-m, -m, n - 1 + m, n - 1 + m, size=SIZE if n <= 30 else 400)
    if n <= 30:  # grid lines, or for larger grids just its square, since lines would crowd out the points
        grid = [svg.line((i, 0), (i, n - 1)) for i in range(n)] + [svg.line((0, i), (n - 1, i)) for i in range(n)]
        svg.add(svg.group(grid, stroke=MUTED, stroke_width=1))
        radius = 0.32
    else:
        svg.add(svg.rect(-m, -m, n, n, fill="#f1f3f5", stroke=MUTED, stroke_width=1))
        radius = 0.5
    svg.add(svg.group((svg.circle((y, n - 1 - x), radius) for x, y in points), fill=EDGE))
    return svg


############
# Families #
############

def ints(constant_id: str, prefix: str) -> list[int]:
    return [int(x) for x in constant_id[len(prefix):].split("-")]


# Each family maps a constant ID to an image, or None if it can't draw that one
FAMILIES: dict[str, tuple[str, Callable[[str], Svg | None]]] = {
    "ramsey": ("ramsey-", lambda c: render_ramsey(c, *ints(c, "ramsey-"))),
    "van-der-waerden": ("van-der-waerden-", lambda c: render_van_der_waerden(c, *ints(c, "van-der-waerden-"))),
    "cage": ("cage-", lambda c: render_cage(c, *ints(c, "cage-"))),
    "degree-diameter": ("degree-diameter-", lambda c: render_degree_diameter(c, *ints(c, "degree-diameter-"))),
    "circle-in-equilateral": ("circle-in-equilateral-", lambda c: render_circle_in_equilateral(c, *ints(c, "circle-in-equilateral-"))),
    "square-packing": ("square-packing-in-square-", lambda c: render_square_packing(c, *ints(c, "square-packing-in-square-"))),
    "kissing-number": ("kissing-number-", lambda c: render_kissing_number(c, *ints(c, "kissing-number-"))),
    "minimal-superpermutation": ("minimal-superpermutation-", lambda c: render_superpermutation(c, *ints(c, "minimal-superpermutation-"))),
    "stamp-folding": ("stamp-folding-", lambda c: render_stamp_folding(c, *ints(c, "stamp-folding-"))),
    "busy-beaver-shift": ("busy-beaver-shift-", lambda c: render_busy_beaver(c, "shift", *ints(c, "busy-beaver-shift-"))),
    "busy-beaver-ones": ("busy-beaver-ones-", lambda c: render_busy_beaver(c, "ones", *ints(c, "busy-beaver-ones-"))),
    "schur": ("schur-", lambda c: render_schur(c, *ints(c, "schur-"), weak=False)),
    "weak-schur": ("weak-schur-", lambda c: render_schur(c, *ints(c, "weak-schur-"), weak=True)),
    "golomb-ruler": ("golomb-ruler-", lambda c: render_golomb_ruler(c, *ints(c, "golomb-ruler-"))),
    "snake-in-the-box": ("snake-in-the-box-", lambda c: render_snake(c, *ints(c, "snake-in-the-box-"), coil=False)),
    "coil-in-the-box": ("coil-in-the-box-", lambda c: render_snake(c, *ints(c, "coil-in-the-box-"), coil=True)),
    "cap-set": ("cap-set-", lambda c: render_cap_set(c, *ints(c, "cap-set-"))),
    "no-three-in-line": ("no-three-in-line-", lambda c: render_no_three_in_line(c, *ints(c, "no-three-in-line-"))),
}


def generate(families: Sequence[str]) -> list[str]:
    """Render every constant these families can draw. Returns the files."""
    with open("_data/constants.yml") as file:
        constant_ids = list(yaml.safe_load(file))
    os.makedirs(GENERATED_IMAGES_DIR, exist_ok=True)
    written = []
    for family in families:
        prefix, render = FAMILIES[family]
        for constant_id in constant_ids:
            if not constant_id.startswith(prefix) or not constant_id[len(prefix):].replace("-", "").isdigit():
                continue
            svg = render(constant_id)
            if svg is None:
                continue
            filename = f"{constant_id}.svg"
            pathlib.Path(GENERATED_IMAGES_DIR, filename).write_text(svg.render())
            written.append(filename)
    print(f"Wrote {len(written)} images to {GENERATED_IMAGES_DIR}/")
    return written


def data_uri(path: str) -> str:
    types = {".svg": "image/svg+xml", ".png": "image/png", ".gif": "image/gif", ".jpg": "image/jpeg", ".jpeg": "image/jpeg"}
    data = base64.b64encode(pathlib.Path(path).read_bytes()).decode()
    return f"data:{types[os.path.splitext(path)[1].lower()]};base64,{data}"


def write_sheet(filenames: Sequence[str], output: str) -> None:
    """A self-contained HTML page showing each generated image next to the
    image the constant uses now, with file sizes."""
    with open("_data/constants.yml") as file:
        constants = yaml.safe_load(file)
    rows = []
    for filename in sorted(filenames, key=lambda f: [int(x) if x.isdigit() else x for x in f[:-4].split("-")]):
        constant_id = filename[:-4]
        generated = os.path.join(GENERATED_IMAGES_DIR, filename)
        current = (constants[constant_id].get("image") or {}).get("path", "").lstrip("/")
        if current == generated:
            status, current_cell = "in use", "<td class='none'>using generated</td>"
        elif current:
            status = "replace?"
            current_cell = (f"<td><img src='{data_uri(current)}'><div>{os.path.getsize(current):,} bytes</div></td>")
        else:
            status, current_cell = "new", "<td class='none'>none</td>"
        rows.append(f"<tr><th>{constant_id}<div>{status}</div></th>"
                    f"<td><img src='{data_uri(generated)}'><div>{os.path.getsize(generated):,} bytes</div></td>{current_cell}</tr>")
    page = f"""<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Generated images</title>
<style>
body {{ font-family: system-ui, sans-serif; margin: 16px; background: #fff; color: #212529; }}
table {{ border-collapse: collapse; }}
th, td {{ border-bottom: 1px solid #dee2e6; padding: 12px; vertical-align: middle; text-align: center; }}
th {{ text-align: left; font-weight: 600; white-space: nowrap; }}
th div, td div {{ font-weight: normal; color: #6c757d; font-size: 0.85em; margin-top: 4px; }}
img {{ max-height: 300px; max-width: min(640px, 70vw); }}
.none {{ color: #adb5bd; }}
</style></head><body>
<h1>Generated images</h1>
<table><tr><th>Constant</th><th>Generated</th><th>Current</th></tr>
{''.join(rows)}
</table></body></html>
"""
    pathlib.Path(output).write_text(page)
    print(f"Wrote {output}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("families", nargs="*", help=f"families to draw (default: all): {', '.join(FAMILIES)}")
    parser.add_argument("--sheet", help="also write an HTML page comparing the images to the current ones")
    args = parser.parse_args()
    unknown = set(args.families) - set(FAMILIES)
    if unknown:
        parser.error(f"unknown families: {', '.join(sorted(unknown))}")
    written = generate(args.families or list(FAMILIES))
    if args.sheet:
        write_sheet(written, args.sheet)


if __name__ == "__main__":
    main()
