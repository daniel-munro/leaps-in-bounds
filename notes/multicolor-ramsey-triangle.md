# Multicolor Ramsey numbers for triangles

## Schur colorings

A Schur coloring of `1, …, m` with `k` colors gives `R_k(3) >= m + 2`, by coloring the edge `uv` of `K_{m+1}` with the color of `|u - v|`. The certificates for `k = 5` to `9` reuse the Schur certificates this way (`format: coloring`), so every new Schur lower bound gives a Ramsey one two higher. From `schur-6-lower-538` and `schur-8-lower-5382` (both from `mckenna-2026`) this gives `R_6(3) >= 540` and `R_8(3) >= 5384`, above the bounds in the survey `ejc-ds1-small-ramsey-numbers` (538 and 5288). For `k = 9` the Schur certificate (17760) is still below the literature's `S(9) >= 17803` (`ageron-et-al-2021`), so `R_9(3) >= 17762` is below the literature's 17805.

For `k <= 4` Schur colorings fall short: `S(3) = 13` and `S(4) = 44` give only 15 and 46. Cyclic colorings (symmetric sum-free partitions of `Z_N \ {0}`) don't help for `k = 4` either: an exhaustive backtracking search (a few seconds in Python) finds none for `N = 49` or `N = 50`.

## Non-linear constructions

- `R_3(3) >= 17`: Greenwood and Gleason's cubic residue coloring of GF(16), as an edge coloring. Every one of its 240 single-edge recolorings has a monochromatic triangle.
- `R_4(3) >= 51` (the literature bound, `chung-1973`): found by local search over colorings with the block structure of Chung's construction, which only has 31 parameters: three copies of the K_16 coloring with its 3 colors mapped into 4 colors, maps for the edges between copies (depending on the color of `xy` in K_16, and a fixed color for the edges between copies of the same vertex), an extra edge, and a color for the edges from each end of it to each copy. Hill climbing with random restarts in Python (numpy for counting triangles) found one on the 4th restart, in about a minute. The parameters are in the certificate's notes.

## Ideas

- Chung's recurrence `R_k(3) >= 3 R_{k-1}(3) + R_{k-3}(3) - 3` with the same block structure might beat the Schur bounds for some `k`, though for `k >= 5` it gives far less than the Schur constructions (Exoo noted it gives only `R_6(3) >= 500`).
- Improving `R_4(3) >= 51` is believed hard: it can't be done with group partitions into symmetric product-free sets (see the survey, section 6.1.1).
