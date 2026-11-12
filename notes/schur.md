# Schur numbers

## Residue templates

Most lower bounds for larger `k` come from a coloring of fewer colors by a template mod `M`: for a Schur coloring `g` of `1, …, N` with `k` colors, the integers `Mq + r` for `q` from `1` to `N` and `r` in a set `R` of representatives get color `g(q)`, and the other residues mod `M` get `m` new colors, each sum-free mod `M`. This works when `r1 + r2 - r3` is never a nonzero multiple of `M` for `r1, r2, r3` in `R`. With every representative in `(-M, 0]`, the length is `M (N + 1) + min(R) - 1`, so `S(k + m) >= M (N + 1) + min(R) - 1`. A positive representative leaves a small integer uncovered, which has to be patched by hand.

- `m = 1`: `M = 3`, `R = {0, -1}`, Schur's `S(k + 1) >= 3 S(k) + 1`.
- `m = 2`: `M = 10`, `R = {-7, -6, -1, 0, 1}`, new colors `{2, 5, 8}` and `{6, 7}`, with the integers 1 and 2 patched: `S(k + 2) >= 10 S(k) + 2`. This is the template of the S(8) >= 5372 coloring (read off from it). With all representatives `<= 0` the best is `M = 9`, `9 S(k) + 3`.
- `m = 3`: `M = 33`, `R = {0, -1, -10, -11, -12, -14, -15, -16, -25, -26}`, new colors `{1, 6, 9, 13, 16, 20, 24, 27, 31}`, `{2, 5, 14, 15, 25, 26}`, `{3, 4, 10, 11, 12, 28, 29, 30}`: `S(k + 3) >= 33 S(k) + 6`, as in `rowley-2019`. Found by a backtracking search in C over residue assignments (a few seconds): `min(R) = -26` is the best for `M = 33`, and nothing exists for `M = 34` with representatives in `(-34, 0]`. Applied to S(6) >= 537, this gives [S(9) >= 17727](../certificates/schur/schur-9-lower-17727.yml) (literature 17803). The `m = 2` template from S(7) >= 1696 gives only 16962, and `3 S(8) + 1` gives 16117.

## Ideas

- `m = 4` from S(5) = 160 would need `M >= 111`; 17803 = 111 * 160 + 43 suggests such a template. The plain backtracking search is too slow for `M` that large; a SAT encoding might work.
