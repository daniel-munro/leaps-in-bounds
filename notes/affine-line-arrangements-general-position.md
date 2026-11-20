# Arrangements of lines in general position

## Verified lower bounds by explicit realizations

A lower bound of `N` is certified by `N` integer arrangements in general position of pairwise different combinatorial types (see the family in [certificates/README.md](../certificates/README.md)).

- 1 to 7 lines: matched (1, 1, 1, 1, 6, 43, 922), with coefficients of at most 12138.
- 8 lines: matched (38609, the 38612 simple arrangements of 8 pseudolines in the plane (A090339) minus the 3 that come from the non-stretchable simple non-Pappus arrangement of 9 projective pseudolines), by a generator: see [below](#all-38609-types-of-8-lines-by-extension-in-the-dual-plane-november-2026).
- 9 lines: 3111341 types, from Christ's database (`christ-2011`). A generator finds 3110345 of them, 996 short: see [below](#9-lines-3110345-types-november-2026).

How the realizations were found (Python, exact rational arithmetic, using `arrangement_type` from `scripts/certificates/families/line_arrangement.py` to tell types apart): extend each arrangement of `n - 1` lines by a line through two random points near its vertices (offsets of `1/3` to `1/1000` in each coordinate), and also delete a random line from the arrangements found so far and add one back. This reached all 922 types of 7 lines in about 30 seconds on 8 cores. Coefficients then grow to dozens of digits, so each arrangement was simplified afterwards: map the bounding box of its vertices to the unit square, scale by increasing factors, round each line's coefficients, and keep the first result of the same type.

## Initial bounds for 8 to 12 lines

Certified with random arrangements of lines `a x + b y = c` (`a` and `b` of absolute value at most `6 + max(0, n - 8)`, `c` at most twice that, kept when in general position), deduplicated by a hash of `arrangement_type`, sized so that the checker takes about 1.5 to 2 minutes of CPU: 8000 for 8 lines (from 11200 draws), 5500 for 9, 4000 for 10, 2700 for 11 and 2000 for 12 (almost no repeats for 9 and more). Coefficients that small can't give every type, so matching 38609 for 8 lines still needs the extension search above, and a faster checker.

## Faster checker (November 2026)

Arrangements in general position are now told apart by `general_arrangement_type`: the order in which the other lines cross each line, read from its first end in a walk around the ends, minimized over the start and direction of the walk. This follows the canonical form in Sami Hani Badaoui and Sarah Ellen Mary Vaughan's C++ checker for ten-line arrangements (pull request #85). It agreed with `arrangement_type` on every one of 3375 random arrangements in general position of 3 to 7 lines, including images under random affine maps (some reversing orientation), rescaled coefficients and renumbered lines, which fell into 189 types under both. It takes about 0.5 ms for 10 lines, against about 10 ms for `arrangement_type`: the 4000-arrangement witness for 10 lines now checks in 2 s instead of 41 s.

At that speed a few hundred thousand arrangements fit in the checker's budget, so 38609 for 8 lines is now within reach, given as a [generator](../certificates/README.md#generators) if the witness is too large. The 113 million arrangements of 10 lines proposed in #85 would still take about 16 hours, so they'd need a vectorized or compiled key, and streaming the generator's output.

## Generator witnesses (November 2026)

The bounds for 10 to 12 lines are now certified by [generators](../certificates/README.md#generators): 700000 for 10 lines, 750000 for 11 and 800000 for 12, increasing with the number of lines. Running the generator and checking its output took 16, 22 and 30 minutes, with 4 such jobs at once on an 8-core laptop; about half the time is the generator, which has to tell types apart too. Each draws random lines `a x + b y = c`, redrawing any line parallel to an earlier one, with `|a|, |b| <= r` and `|c| <= 2 r` for `r` from `n - 3` to `n`, and prints the arrangement when it's in general position and its `general_arrangement_type`, computed the same way with integers, is new. Redrawing parallel lines rather than rejecting the whole arrangement matters: for 12 lines, about 70% of draws are then in general position with `r = 9`, and the generator became about 25 times faster. The generators of the [other family](affine-line-arrangements.md#generator-witnesses-november-2026) use the same program.

The limits now are the checker's time and memory (about 1.5 to 1.7 GB per million arrangements), and the 200 MB limit on a generator's output, about 2 million arrangements of 12 lines. Matching 38609 for 8 lines with random draws looks slow: they found 32000 types in about a minute, but new ones were getting rare.

## Streaming checker (November 2026)

Prompted by pull request #98, which submits a generator for 56,500,001 types of 10 lines that prints 136.5 million random arrangements (19.8 GB), with repeats. The checker now:

- reads a generator's output as a stream, so the 200 MB limit doesn't apply to this family;
- accepts witnesses with repeated types, counting the distinct ones, by an 8-byte hash of each canonical form (a shared hash only undercounts), kept sorted in a numpy array: 8 bytes per arrangement, instead of about 1.6 kB;
- checks batches of 10000 arrangements in parallel, one process per core;
- computes `general_arrangement_type` about 4.7 times faster (0.074 ms for 10 lines, from 0.35 ms): crossings and ends are sorted with floats and then checked exactly, falling back to exact sorting if they're out of order or tied, and since no two lines are parallel, each walk meets every line in its first n steps, so the walk is a slice and the renumbering is a `bytes.translate`.

The new key agreed exactly with the old one on 4784 random arrangements (2563 in general position), and the hashed counts matched the old exact counts on 100000 arrangements shaped like #98's (99566 types) and 18293 mixed arrangements, mostly not in general position (18290 types). A million arrangements of 10 lines in general position took 27 s from a generator on an 8-core laptop, so #98's 136.5 million should take under an hour.

## All 38609 types of 8 lines, by extension in the dual plane (November 2026)

`affine-line-arrangements-general-position-8-lower-38609` matches the known value, with a [generator](../certificates/README.md#generators) that takes about 8 minutes of CPU, almost all of it the generator (on an 8-core laptop with a load of about 80 from other jobs). It is a systematic version of the extension search above:

1. Start from the 922 arrangements of 7 lines in the existing witness (embedded in the generator, xz and base85, 16 kB).
2. Add a line in every possible way. A new line `y = m x + k` is a point `(m, k)` of a dual plane, where the lines through a vertex `(x0, y0)` form the dual line `k = y0 - m x0`, and the lines parallel to a line of slope `s` form the dual line `m = s`. The new arrangement's type is the same throughout each cell of this dual arrangement, so one point per cell gives every extension of the given realization: take a point inside each edge of the dual arrangement and step off it on both sides, by less than the distance to any other dual line (shear the arrangement first so no line is vertical). With exact fractions, this took about 2 minutes, about 1000 points per arrangement, and gave 38551 types.
3. The last 58 come from changing which line is at infinity: an arrangement of `n` lines in general position is a simple arrangement of `n + 1` projective lines with one marked, so a projective map that takes line `i` to infinity (and the line at infinity to an ordinary line) gives another type of the same projective arrangement. One pass of this over the 38551 found all 58 (about 2.5 minutes).

Each arrangement found is rounded to small coefficients when that keeps its type (map the box around its vertices to the unit square, scale by `2 * 1.25^j` and round), which takes about as long as the search. Coefficients are mostly under a few hundred, with a few up to `2 * 10^8` where rounding failed.

Didn't work as well: deleting a random line from an arrangement found and adding one back in every cell (as for 7 lines) found the missing types slowly, 41 of the 58 in about 13 minutes (on a busy machine), with new ones getting rare; random draws with `|a|, |b| <= 9` found 12 new types in 1.7 million draws. Marking a different line at infinity is far better at filling in the rare types.

## 9 lines: 3110345 types (November 2026)

`affine-line-arrangements-general-position-9-lower-3110345` is a generator that first does the search for 8 lines above (all 38609 types), then:

1. Adds a ninth line to each arrangement of 8 lines in each cell of its dual arrangement (about 470 cells), as above but with floating point in numpy. The new line is `a x + b y = c` with `b` a power of 2, as small as keeps `(-a / b, c / b)` in the same cell, so it has up to 10 digits. Before printing, exact integer arithmetic checks that it is parallel to no line and misses every vertex.
2. Marks each of the 9 lines of each new arrangement as the line at infinity (an exact projective map, vectorized in int64 when the coefficients are below `2^30`). One level of this, without repeating it on the arrangements it finds, multiplied the yield: the first 1000 arrangements of 8 lines gave 1.05 million types, against 205000 from step 1 alone.

Arrangements are printed when their form is new, by `general_arrangement_type` computed with floats for a batch of arrangements at once (sorting crossings and ends with `argsort`, and comparing walks first by the crossings of their first two lines, which is about 2.3 times faster than comparing all 36 walks in full). It agreed byte for byte with the exact form on 100000 arrangements, and the first 300000 rows printed were 300000 types by the checker's form. The types found grew as 1.05 million after 1000 arrangements of 8 lines, 2.56 million after 5000, 2.94 million after 10000, 3.09 million after 20000, and 3110345 after all 38609. Running it took about 30 minutes of CPU (8 for the 8-line search) on a busy laptop, and printed 354 MB; checking that took about 11 more.

Didn't work as well: step 1 alone, without step 2, had found 2.06 million types when stopped (partway through the arrangements of 8 lines), with new ones getting rarer. Random draws find new types for 9 lines easily but would need far more draws to fill in the rare ones.

To get the last 996, repeating step 2 on the arrangements it finds is the obvious next try (it snowballed when tried on a small sample, so it needs a budget), or deleting a line and adding one back as for 8 lines.

## Ideas

- For 10 lines, nothing is known beyond bounds that follow from projective counts: each simple arrangement of 11 projective lines (41693377 of them, Aichholzer and Krasser) gives between 1 and 11 affine types by choosing the line at infinity.
