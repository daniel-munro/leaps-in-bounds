# Cages

## Initial upper bounds (November 2026)

An AI agent (Claude) added first verified upper bounds for many `cage-{k}-{g}`. It wrote the generators in Python plus a small C program, and didn't keep them in the repository. Everything below can be rebuilt from the descriptions in the certificates' `notes`.

### Algebraic constructions (fast, and they match the literature where marked)

- **Girth 5, amalgams:** points `(x,y)` with `x` in `0..k-3`, lines `[m,b]` with `m` in `0..k-3`, and `y, b` in `Z_q` for the smallest prime `q >= max(k-2, 5)`. Join `(x,y) ~ [m,b]` when `y = mx + b`, plus the inner cycles `(x,y) ~ (x,y±1)` and `[m,b] ~ [m,b±2]`. This gives a `k`-regular graph of girth 5 on `2(k-2)q` vertices, since a 4-cycle would need `±1 = ±2`. It matches n(5,5) = 30 and n(6,5) = 40, and is 5 to 50% above the records for k = 8..20. The inner graphs are Cayley graphs on an abelian group, so each block can only carry a cycle (degree 2). Getting closer to the records needs the field-based inner graphs of the elliptic-semiplane papers (Funk; Abajo, Araujo-Pardo, Balbuena and others).
- **(4,5): the Robertson graph**, from the 19-cycle with chords `i ~ i + c_i`. The chord list I first remembered was wrong (it gave girth 4). The working one is in the certificate.
- **Girth 6, k-1 not a prime power:** the biaffine plane over GF(q) restricted to `k` slopes and `k` x-values, giving `2kq` vertices for the smallest prime power `q >= k`. This lands 2 to 18 above the literature. The `2(kq-2)`-type constructions and O'Keefe-Wong's 90 for k = 7 were not tried.
- **Girth 8:**
  - `k = q+1` with q a prime power: the incidence graph of W(q). Its lines are the totally isotropic lines of PG(3,q) for `x0y1 - x1y0 + x2y3 - x3y2`.
  - `k = q`: delete from W(q) the points collinear with a point P and the lines meeting a line L through P. This leaves a q-regular graph of girth 8 on `2q^3` vertices.
  - k = 15: also remove a perfect matching. This verified but was then dropped as too slow (see below).
- **Girth 12, k = q+1:** the incidence graph of the split Cayley hexagon H(q). Points are on `X0X4 + X1X5 + X2X6 = X3^2`, and lines are the lines on it with `p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31`. The last equation is often misremembered as `p46=p03`, which gives the wrong number of lines. These give 126, 728 and 2730, matching the literature.

### Cyclic voltage lifts (everything else)

For girth 7, 9, 10, 11 and 13 to 16, the graphs are lifts of a small base graph over `Z_m`:
- K_{k+1} for g <= 10;
- Petersen, Heawood or the incidence graph of PG(2,3) for larger g;
- the Robertson graph or the (5,5) amalgam for odd g >= 11.

The search is min-conflicts: fix the voltages on a spanning tree to 0, and for each other edge in random order count, for every voltage, the closed non-backtracking walks shorter than g through that edge that it would make zero. Pick a least-conflict voltage, with 5% random moves. A full sweep with no conflicts means girth >= g, and an exact lift BFS then confirms girth == g. Each m was given 30 to 200 s of CPU, stepping m down by about 7% until it failed.

An abelian lift has a zero-voltage closed walk of length `2(a+b+c)` for every theta subgraph with paths of lengths a, b, c. So lifts of K_{k+1} have girth at most 10, and a base with larger girth is needed for larger g.

Results:

| Girth | Base | Values (vs literature) |
| --- | --- | --- |
| 7 | K_{k+1} | (4,7) = 120 (67), (5,7) = 180 (152), (6,7) = 490 (294), (7,7) = 1096, (8,7) = 2142, (9,7) = 4030, (10,7) = 7051, (11,7) = 10704, (12,7) = 17173, (13,7) = 26040 |
| 9 | K_{k+1} | (3,9) = 60 (58), (4,9) = 325 (270), (5,9) = 1434 |
| 10 | K_{k+1} | (3,10) = 72 (70), (4,10) = 450 (320), (5,10) = 2484 (1296), (6,10) = 11200 |
| 11 | Petersen | (3,11) = 220 (112) |
| 11 | Robertson | (4,11) = 2793 |
| 13, 15 | Petersen | (3,13) = 490 (272), (3,15) = 920 (620) |
| 14, 16 | Heawood | (3,14) = 616 (384), (3,16) = 1540 (936) |

Failures:

- (4,13) on the Robertson graph, up to n = 12863.
- (4,14) on PG(2,3) and W(3), up to n = 9680.
- (5,11) on the (5,5) amalgam, up to n = 13530.

The m needed grows roughly like `W^0.64`, where W is the number of closed non-backtracking walks shorter than g per base vertex. For K_{k+1} and g = 7, W is about `k^5`. So lifts get far from the Moore bound as k grows: about 2.3x the Moore bound for (4,7) and 7.7x for (10,7). Cubic cases come out 1.03x to 2x the records.

### What failed or was skipped, and why

- **The size of graph the checker can handle.** The checker's girth test runs a BFS from every vertex, to depth about g/2, on Python big integers. Its cost is roughly `n * (1 + k + ... + k(k-1)^(floor((g-2)/2)-1)) * n/64`. Measured CPU times:
  - W(13) minus a flag (13,8), n = 4394: 32 s.
  - W(13) (14,8), n = 4760: 47 s.
  - (13,7) lift, n = 26040: 59 s.
  - (6,10) lift, n = 11200: 78 s, kept but the slowest.

  Girth 7 is cheap per vertex because the BFS depth is only 2. A lift of K_15 for (14,7) would need about 36000 vertices, and an estimated 150 s or more.
  - H(5) (6,12), n = 7812: 190 s, so it was dropped.
  - (15..20, 8) from W(16), W(17) and W(19), n = 8192 to 14480: well over 2 minutes, so dropped.

  A faster checker, such as one using numpy or a compiled BFS, would make these certifiable at once.
- **Lifts that need too many vertices:** g = 7 for k >= 14, g = 9 for k >= 8, g = 10 for k >= 7, g = 11 for k >= 5, g = 13 to 16 for k >= 4 ((4,15) and (4,16) were not tried). Abelian lifts of small bases need well beyond the checkable size there. Better ideas:
  - non-abelian voltage groups;
  - Cayley graphs of PSL(2,q);
  - lifts of a good (k,g-1) or (k,g-2) graph instead of K_{k+1};
  - known algebraic families, such as excisions from generalized polygons for (k,10) and (k,11), or Lazebnik-Ustimenko-Woldar graphs for large even g.
- **Matching the literature for small cases** (for example (4,7) = 67, (3,13) = 272, (3,14) = 384, (4,9) = 270, (4,10) = 320) needs the published constructions. These are mostly Exoo's voltage graphs over non-cyclic groups, or tailored base graphs.
