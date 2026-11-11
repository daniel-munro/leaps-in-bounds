# Arrangements of lines in the affine plane

## Verified lower bounds by explicit realizations

A lower bound of `N` is certified by `N` integer arrangements of pairwise different combinatorial types (see the family in [certificates/README.md](../certificates/README.md)). The known values for up to 7 lines are all realizable: an arrangement of `n` affine lines is an arrangement of `n + 1` projective lines with one marked as the line at infinity, and every arrangement of at most 8 pseudolines is stretchable (Goodman and Pollack). So matching the literature is a matter of finding a realization of every type.

- 1 to 6 lines: matched (1, 2, 4, 9, 47, 791), with coefficients of at most 16.
- 7 lines: not yet. The grid search found 34594 of the 37830 types in about 5 rounds of 96000 random arrangements each, while the machine was busy, and was still finding a few hundred new types per round when stopped. Continuing it, then extending the 6-line types by special lines to fill in the rest, looks feasible. The checker takes about 3 ms per arrangement of 7 lines, so a certificate would take about 2 minutes to check.

How the realizations were found (Python, exact rational arithmetic, using `arrangement_type` from `scripts/certificates.py` to tell types apart):

1. Random subsets of the lines through two points of a `k x k` grid, `k` from 3 to 6. Small grids have lots of concurrencies and parallels, so this finds almost every degenerate type with tiny coefficients: 790 of the 791 types of 6 lines in under a minute on 8 cores. The one it missed was 6 parallel lines.
2. Extending arrangements of `n - 1` lines by one line: through two vertices, through a vertex parallel to a line or in a direction between two critical directions there, parallel to a line between two vertex offsets, or through two random points near vertices.

Rounding to small integers works for arrangements in general position, but not for degenerate ones, since rounding breaks the concurrencies. Extending by lines through vertices makes coefficients grow quickly (to 20 digits for 6 lines), so the grid search is the better source of degenerate types.

## Initial bounds for 7 to 12 lines

Certified with random arrangements, without trying to reach every type, sized so that the checker takes about 1.5 to 2 minutes of CPU (it measured about 8 ms per arrangement of 7 lines and 12 ms of 8 on a busy machine, rising to roughly 50 ms for 12): 12000 for 7 lines, 8000 for 8, 5500 for 9, 4000 for 10, 2700 for 11 and 2000 for 12. Each arrangement is, with probability 0.7, lines through random pairs of points of a `k x k` grid (`k` from 3 to 6), and otherwise random lines in general position with small coefficients; types were deduplicated by a hash of `arrangement_type`. For 7 lines, 28760 draws gave the 12000 types; for 8 lines and more almost every draw is a new type, so the counts are limited only by the checker's time. Files are 80 to 100 kB with xz, so a faster checker (the canonical form tries `4n` relabelings with exact fractions) would allow much more.

## Ideas

- 8 lines: Finschi's table (`finschi-2001`, Table 8.1) has 4134939 abstract types not all parallel, so at most 4134940 combinatorial types, minus at least one for each of the 274 non-realizable oriented matroids of rank 3 on 9 elements. A lower bound needs realizations of millions of types, too many for a witness file of reasonable size. A lower bound of 460780 follows from the 460779 realizable arrangements of 9 projective lines (plus all lines parallel) but isn't in the literature as such.
