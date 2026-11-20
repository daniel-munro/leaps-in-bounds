# Map folding

## Status

- Lower bounds certified by listing every folding (exact counts) for 2 × 2 to 2 × 8, 3 × 3 and 4 × 4, matching OEIS A001415 and A001418. The largest (2 × 8, 320,896 foldings) is 330 kB with xz.
- 3 × 4 (15,552) and 3 × 5 (201,240, 224 kB with xz): every folding listed, now that the literature has A001416 (November 2026).
- 2 × 9, 2 × 10, 3 × 6 and 4 × 5 (November 2026): every folding, printed by generators (`format: generator`, output `stacks`) written by an AI agent (Claude Opus 5.5). The search inserts the cells into the stack one at a time in row-major order. Inserting cell k adds creases to its left and upper neighbours; a gap is allowed for one of them when it's in the same region of the nested creases already on that edge as the neighbour, found by one scan of the stack per edge. Crossings among placed creases can't be undone by later insertions, so this finds every folding once. Generating and checking, on a busy machine: 2 × 9 (1,787,904, 34 MB) about 2 minutes; 3 × 6 (2,016,432, 38 MB) about 2 minutes; 4 × 5 (6,139,920, 129 MB) about 10 minutes and 1.8 GB of memory; 2 × 10 (9,381,840, 197 MB, just under the 200 MB limit) about 19 minutes (8 minutes of CPU) and 2.6 GB.
- Larger counts (3 × 7, 21,582,624 foldings, 475 MB; 2 × 11, 1.2 GB; 4 × 6, 2.1 GB) are over the 200 MB the folding checker reads at once; listed in `certificates/blocked.yml`.

## Initial bounds for maps with no known count (November 2026)

The literature now has 3 × 4 to 3 × 14 (A001416) and 4 × 5 to 4 × 8, 4 × 10, 5 × 6 to 5 × 8 and 6 × 7 (a table on Code Golf Stack Exchange, question 276709; its 4 × 9 entry conflicts with its 9 × 4 entry, so it wasn't added). For the rest, an AI agent (Claude) added:

- **Upper bounds:** the trivial (mn)! in Lean (`MapFoldingFactorial.lean`, using `StampFoldingSmall.count_le`). The factorial is checked by `rfl` with `maxRecDepth` raised, about a second for 126!.
- **Lower bounds:** witnesses listing products of strip foldings. For foldings `s` of the strip of `n` and `t` of the strip of `m` (levels `s(j)`, `t(i)`), the cell `(i, j)` at level `t(i) n + s(j)` for even `i` and `t(i) n + n - 1 - s(j)` for odd `i` is a folding: fold every row the same way, then fold the strip of rows. The same with rows and columns swapped gives as many more, and the two sets don't overlap for `m, n >= 2` (a row and a column can't both be contiguous in the stack). So there are at least `2 s(m) s(n)` foldings, but this isn't proved here: the witnesses list the first products in lexicographic order, as many as fit in about 430 kB with xz (80000 to 120000). The checker now accepts cells as comma-separated decimals for maps of more than 36 cells.

## More products, from generators (November 2026)

Generators (`format: generator`) written by an AI agent (Claude Opus 5.5) print many more of these products, raising every lower bound from the product witnesses above: all 2 s(m) s(n) products where they fit in 200 MB of output (4 × 9: 145,152; 4 × 11: 1,481,920; 5 × 9: 453,600; 5 × 10: 1,406,000; 6 × 8: 400,896; 6 × 9: 1,306,368), and otherwise as many as fit, half of each kind (from 1,590,000 for 3 × 15, down to 500,000 for 7 × 18, where each stack takes 394 bytes). The limit is the 200 MB the folding checker reads at once, not the generator, which takes seconds: it lists the foldings of the shorter strip, loops over those of the longer strip as a depth-first search finds them, and writes each row once per strip folding, so that each product is a join of the rows in the order of the other strip folding. Generating and checking each took 1 to 5 minutes, on a heavily loaded machine. The older 60,000 to 120,000 product witnesses are kept, though superseded.

## Ideas

- A streaming folding checker would allow 3 × 7 and 2 × 11 (maybe 30 to 60 minutes each at the current checker's speed, about 30 to 60 µs per stack) and many more products for the maps with no known count. Distinctness needs either a set of hashes of the stacks (8 bytes each would still be 400 MB for 50 million) or stacks in increasing order, which the generators here don't print. A more compact format would also help the products under the current limit: comma-separated decimals take about 2.8 bytes per cell for maps of 50 to 126 cells, where two base-36 characters per cell with no separators would take 2, about 40% more stacks.
- A Lean proof of `count m n >= 2 * count 1 m * count 1 n` (the product construction above) would give much better lower bounds from the stamp counts, once those are proved in Lean.
- As for stamps, upper bounds need a verified counting procedure in Lean.
