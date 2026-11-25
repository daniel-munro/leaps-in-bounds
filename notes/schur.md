# Schur numbers

## Residue templates

Most lower bounds for larger `k` come from a coloring of fewer colors by a template mod `M`: for a Schur coloring `g` of `1, …, N` with `k` colors, the integers `Mq + r` for `q` from `1` to `N` and `r` in a set `R` of representatives get color `g(q)`, and the other residues mod `M` get `m` new colors, each sum-free mod `M`. This works when `r1 + r2 - r3` is never a nonzero multiple of `M` for `r1, r2, r3` in `R`. With every representative in `(-M, 0]`, the length is `M (N + 1) + min(R) - 1`, so `S(k + m) >= M (N + 1) + min(R) - 1`. A positive representative leaves a small integer uncovered, which has to be patched by hand.

- `m = 1`: `M = 3`, `R = {0, -1}`, Schur's `S(k + 1) >= 3 S(k) + 1`.
- `m = 2`: `M = 10`, `R = {-7, -6, -1, 0, 1}`, new colors `{2, 5, 8}` and `{6, 7}`, with the integers 1 and 2 patched: `S(k + 2) >= 10 S(k) + 2`. This is the template of the S(8) >= 5372 coloring (read off from it). Applied to S(6) >= 538, it gives [S(8) >= 5382](../certificates/schur/schur-8-lower-5382.yml), the literature bound, with 1 and 2 getting the two new colors (found by trying all 64 pairs). With all representatives `<= 0` the best is `M = 9`, `9 S(k) + 3`.
- `m = 3`: `M = 33`, `R = {0, -1, -10, -11, -12, -14, -15, -16, -25, -26}`, new colors `{1, 6, 9, 13, 16, 20, 24, 27, 31}`, `{2, 5, 14, 15, 25, 26}`, `{3, 4, 10, 11, 12, 28, 29, 30}`: `S(k + 3) >= 33 S(k) + 6`, as in `rowley-2019`. Found by a backtracking search in C over residue assignments (a few seconds): `min(R) = -26` is the best for `M = 33`, and nothing exists for `M = 34` with representatives in `(-34, 0]`. Applied to S(6) >= 537, this gave [S(9) >= 17727](../certificates/schur/schur-9-lower-17727.yml), and applied to S(6) >= 538 it gives [S(9) >= 17760](../certificates/schur/schur-9-lower-17760.yml) (literature 17803). The `m = 2` template from S(7) >= 1696 gives only 16962, and `3 S(8) + 1` gives 16117.

## Sources of verified bounds

- [S(6) >= 538](../certificates/schur/schur-6-lower-538.yml) is the colouring from `mckenna-2026` (https://github.com/mysticflounder/schur-538), which also has a Lean proof. It was found by searching Prove2Me's Formalpedia (https://prove2.me/formalpedia), which has it as `ClassicalSchur.schur_six_538`, with a statement the same as `LowerBound 6 538`. On 2026-11-12, Formalpedia had nothing else that gives a Schur bound: its `schur_number_exact` (S(5) = 160) was retired as a defective statement.

## Ideas

- `m = 4` from S(5) = 160 would need `M >= 111`; 17803 = 111 * 160 + 43 suggests such a template. The plain backtracking search is too slow for `M` that large; a SAT encoding might work.

## Extension to k = 10..14 (2026-11-25)

The `schur` and `weak-schur` families were extended from k <= 9 to k <= 14. A literature review for the new constants found these stated lower bounds (all in `literature/bounds/`):

- S(10..14): Ageron et al. (arXiv:2112.03175, Tables 1 and 3; the same in v1 and v2) give 60948, 203828, 644628, 2011290 and 6765288, mostly from `S(k + 5) >= 380 S(k) + 148`, and list Rowley's 60320, 201696 and 637856 for k = 10..12 as the previous state of the art. Rowley's own papers state only Ramsey bounds (R_10(3) >= 60322, R_11(3) >= 201698, R_12(3) >= 631842 in arXiv:1912.01164) and the recurrence `S(k + 5) >= 376 S(k) + 160` (arXiv:2107.03560). The 2026 S(6), S(7) and S(8) records were turned into S(11) >= 204208 and S(13) >= 2042082 (Chen, Zhu and Long), S(13) >= 2038282 (Bengone et al.), S(11) >= 204588 and S(13) >= 2045882 (McKenna, Zenodo v1.1.0) and S(12) >= 645388 (Özdemir, Zenodo, from S(7) >= 1698, which is also new for S(7)). Nobody has stated S(10) or S(14) bounds since Ageron et al.
- WS(10..14): Rowley (arXiv:2011.11292) states WS(10) >= 70778 (70782 in v1-v3, from an S(9) value 1 too large). Ageron et al. give 71256, 243794, 815314 (Table 2) and, as the largest entries of Table 4, WS(13) >= 2649772 and WS(14) >= 8560800; these are the only stated bounds for WS(13) and WS(14). Özdemir gives WS(10) >= 71340 = 42 * 1698 + 24.
- Upper bounds for both families at k = 10..14 are the general formulas already used for k <= 9 (Schur, Greenwood-Gleason, Irving, Wan, Fettes-Kramer-Radziszowski via `S(k) <= R_k(3) - 2`, and Irving and Bornsztein for WS), evaluated; no source states a better bound for these k.
- Not recorded because no source states them: values from Abbott-Hanson, Fredricksen-Sweet or the WS recurrences (`WS(n + 1) >= 4 S(n) + 2`, `WS(n + 2) >= 13 S(n) + 8`, `WS(n + 3) >= 42 S(n) + 24`) applied to the newer S records, and `WS(n) >= S(n)`.
