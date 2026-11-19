# Arrangements of lines in general position

## Verified lower bounds by explicit realizations

A lower bound of `N` is certified by `N` integer arrangements in general position of pairwise different combinatorial types (see the family in [certificates/README.md](../certificates/README.md)).

- 1 to 7 lines: matched (1, 1, 1, 1, 6, 43, 922), with coefficients of at most 12138.
- 8 lines: not yet tried at scale. The value 38609 is the 38612 simple arrangements of 8 pseudolines in the plane (A090339) minus the 3 that come from the non-stretchable simple non-Pappus arrangement of 9 projective pseudolines. So all 38609 are realizable, and a witness of a few MB would match it.
- 9 lines: 3111341 types, from Christ's database (`christ-2011`). A witness would be hundreds of MB, so it would need a more compact format.

How the realizations were found (Python, exact rational arithmetic, using `arrangement_type` from `scripts/certificates/families/line_arrangement.py` to tell types apart): extend each arrangement of `n - 1` lines by a line through two random points near its vertices (offsets of `1/3` to `1/1000` in each coordinate), and also delete a random line from the arrangements found so far and add one back. This reached all 922 types of 7 lines in about 30 seconds on 8 cores. Coefficients then grow to dozens of digits, so each arrangement was simplified afterwards: map the bounding box of its vertices to the unit square, scale by increasing factors, round each line's coefficients, and keep the first result of the same type.

## Initial bounds for 8 to 12 lines

Certified with random arrangements of lines `a x + b y = c` (`a` and `b` of absolute value at most `6 + max(0, n - 8)`, `c` at most twice that, kept when in general position), deduplicated by a hash of `arrangement_type`, sized so that the checker takes about 1.5 to 2 minutes of CPU: 8000 for 8 lines (from 11200 draws), 5500 for 9, 4000 for 10, 2700 for 11 and 2000 for 12 (almost no repeats for 9 and more). Coefficients that small can't give every type, so matching 38609 for 8 lines still needs the extension search above, and a faster checker.

## Faster checker (November 2026)

Arrangements in general position are now told apart by `general_arrangement_type`: the order in which the other lines cross each line, read from its first end in a walk around the ends, minimized over the start and direction of the walk. This follows the canonical form in Sami Hani Badaoui and Sarah Ellen Mary Vaughan's C++ checker for ten-line arrangements (pull request #85). It agreed with `arrangement_type` on every one of 3375 random arrangements in general position of 3 to 7 lines, including images under random affine maps (some reversing orientation), rescaled coefficients and renumbered lines, which fell into 189 types under both. It takes about 0.5 ms for 10 lines, against about 10 ms for `arrangement_type`: the 4000-arrangement witness for 10 lines now checks in 2 s instead of 41 s.

At that speed a few hundred thousand arrangements fit in the checker's budget, so 38609 for 8 lines is now within reach, given as a [generator](../certificates/README.md#generators) if the witness is too large. The 113 million arrangements of 10 lines proposed in #85 would still take about 16 hours, so they'd need a vectorized or compiled key, and streaming the generator's output.

## Ideas

- 8 lines: the same search, run from the 922 types of 7 lines, should work. Use `general_arrangement_type` to tell types apart, and plan to simplify coefficients as types are found rather than at the end, since large coefficients slow the checks down.
- For 10 lines, nothing is known beyond bounds that follow from projective counts: each simple arrangement of 11 projective lines (41693377 of them, Aichholzer and Krasser) gives between 1 and 11 affine types by choosing the line at infinity.
