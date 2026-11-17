# Map folding

## Status

- Lower bounds certified by listing every folding (exact counts) for 2 × 2 to 2 × 8, 3 × 3 and 4 × 4, matching OEIS A001415 and A001418. The largest (2 × 8, 320,896 foldings) is 330 kB with xz.
- The same search gives 15,552 foldings of 3 × 4 and 201,240 of 3 × 5, which agree with OEIS A001416, but the 3 × n row has no literature rows yet, so no certificates were added for it: a certificate there would be counted as the bound's discovery. Add the A001416 terms (to 3 × 14, by Lunnon and Irvine) to `literature/bounds/map-folding.csv` first.
- Larger maps are beyond the 500 kB limit for a full list.

## Initial bounds for maps with no known count (November 2026)

The literature now has 3 × 4 to 3 × 14 (A001416) and 4 × 5 to 4 × 8, 4 × 10, 5 × 6 to 5 × 8 and 6 × 7 (a table on Code Golf Stack Exchange, question 276709; its 4 × 9 entry conflicts with its 9 × 4 entry, so it wasn't added). For the rest, an AI agent (Claude) added:

- **Upper bounds:** the trivial (mn)! in Lean (`MapFoldingFactorial.lean`, using `StampFoldingSmall.count_le`). The factorial is checked by `rfl` with `maxRecDepth` raised, about a second for 126!.
- **Lower bounds:** witnesses listing products of strip foldings. For foldings `s` of the strip of `n` and `t` of the strip of `m` (levels `s(j)`, `t(i)`), the cell `(i, j)` at level `t(i) n + s(j)` for even `i` and `t(i) n + n - 1 - s(j)` for odd `i` is a folding: fold every row the same way, then fold the strip of rows. The same with rows and columns swapped gives as many more, and the two sets don't overlap for `m, n >= 2` (a row and a column can't both be contiguous in the stack). So there are at least `2 s(m) s(n)` foldings, but this isn't proved here: the witnesses list the first products in lexicographic order, as many as fit in about 430 kB with xz (80000 to 120000). The checker now accepts cells as comma-separated decimals for maps of more than 36 cells.

## Ideas

- A Lean proof of `count m n >= 2 * count 1 m * count 1 n` (the product construction above) would give much better lower bounds from the stamp counts, once those are proved in Lean.

## Ideas

- As for stamps, upper bounds need a verified counting procedure in Lean.
