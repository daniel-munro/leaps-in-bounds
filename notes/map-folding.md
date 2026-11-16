# Map folding

## Status

- Lower bounds certified by listing every folding (exact counts) for 2 × 2 to 2 × 8, 3 × 3 and 4 × 4, matching OEIS A001415 and A001418. The largest (2 × 8, 320,896 foldings) is 330 kB with xz.
- The same search gives 15,552 foldings of 3 × 4 and 201,240 of 3 × 5, which agree with OEIS A001416, but the 3 × n row has no literature rows yet, so no certificates were added for it: a certificate there would be counted as the bound's discovery. Add the A001416 terms (to 3 × 14, by Lunnon and Irvine) to `literature/bounds/map-folding.csv` first.
- Larger maps are beyond the 500 kB limit for a full list.

## Ideas

- As for stamps, upper bounds need a verified counting procedure in Lean.
