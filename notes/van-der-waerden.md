# Van der Waerden numbers

Constants are `van-der-waerden-{r}-{k}`: `r` colors, progressions of length `k`.

## Rabung colorings and zips

For a prime `p` with `r | p - 1` and a primitive root `g`, color each `x` that isn't a multiple of `p` by `(log_g(x mod p) + s(x mod m)) mod r`, a coloring with period `m p`, for a zip factor `m` coprime to `p` and offsets `s: Z_m -> Z_r` (`m = 1` is Rabung's construction). Take the integers `0` to `(k - 1) m p`, color the multiples of `p` by backtracking, then extend greedily at both ends. Checking a candidate `(p, m, s)` against the whole string, with the multiples of `p` left uncolored, takes seconds up to `10^5` integers.

For `m = 1`, a quick filter: the coloring works for all progressions with difference not divisible by `p` exactly when no `k` cyclically consecutive residues have their nonzero members all the same color.

The bounds of `rabung-lotts-2012` all come out of this with `value - 2 = (k - 1) m p`, so factoring `value - 2` gives `p` and `m`. Reproduced exactly, with the offsets found by trying all `r^(m-1)` of them:

| Bound | `p` | `g` | `m` | `s(0..m-1)` |
| --- | --- | --- | --- | --- |
| W(3,5) >= 2174 | 181 | 2 | 3 | 0 1 2 |
| W(3,6) >= 11192 | 373 | 2 | 6 | 0 0 1 1 2 2 |
| W(3,7) >= 48812 | 1627 | 3 | 5 | 0 0 0 0 1 |
| W(3,9) >= 932746 | 116593 | 10 | 1 | 0 |
| W(3,10) >= 4173725 | 463747 | 3 | 1 | 0 |

The first matching `s` worked each time, and the multiples of `p` always had a valid coloring. `W(3,11) >= 18603732` is `m = 1` with `p = 1860373` too. Its witness would compress to roughly 500 kB with xz (judging by 124 kB for `W(3,10)`), at the size limit, and the checker in `scripts/certificates.py` would take hours on it.

No plain Rabung prime (`m = 1`) gets close for 3 colors: the best for `W(3,5)` is `p = 241` (964 integers), and for `W(3,7)` it's `p = 7309` (43854).

## Product constructions

- `blankenship-c-t-2018`: for a prime `p <= k`, `W(r,k) > p (W(r - ceil(r/p), k) - 1)`. Integer `p q + j` gets the color of `q` in the smaller coloring, relabeled into a set of colors for residue `j`, so that no color is used for all residues. `W(6,3) >= 226` is this with `p = 3` from `W(4,3) >= 76`. `W(5,6) >= 786741` is `p = 5` from `W(4,6) >= 157349`, which has no witness here yet.
- Xu's recursion, `W(st,k) > p (W(t,k) - 1) + 1` (per Monroe, arXiv:1603.03301): color `x` by the pair (Rabung `s`-coloring of `x mod p`, `t`-coloring of `floor(x / p)`). `W(4,7) >= 2284752` is `p = 617` with `W(2,7) >= 3704`.

## Checker budget and initial bounds

The checker in `scripts/certificates.py` does `k - 1` shifts and ANDs of an `n`-bit integer for each color and each difference, so its time grows like `r n^2` and doesn't depend on `k`: about 80 s of CPU for `r n^2 = 1.3 * 10^12` (`n` about 658k for 3 colors, 570k for 4, 510k for 5, 465k for 6). Witnesses of that size compress to 20 to 30 kB with xz, so time, not the size limit, is what binds. Every constant whose record is beyond this budget got an initial bound at the budget:

- Plain Rabung (`m = 1`), with the largest prime `p = 1 mod r` below `budget / (k - 1)` that passes the window filter (a few seconds each to find): W(3,11) p = 65809, W(4,8) 81401, W(4,9) 71257, W(4,10) 63337, W(4,11) 56993, W(5,7) 84751, W(5,8) 72661, W(5,9) 63691, W(5,10) 56611, W(5,11) 50971, W(6,7) 77569, W(6,8) 66463, W(6,9) 58171, W(6,10) 51691, W(6,11) 46507. The multiples of `p` can get any color, since the filter already breaks every progression with difference not divisible by `p`.
- Truncated products: W(5,6) >= 509901 is `blankenship-c-t-2018` with `p = 5` on the first 101980 integers of the W(4,6) witness (the whole witness would give 786051 but take about 3 minutes to check); W(6,6) >= 465373 is Xu's recursion with `p = 139` on the first 3348 integers of the W(3,6) witness (all of it gives the record 1555550).

Largest primes passing the Rabung filter (`m = 1`) for small cases: W(2,5) 37, W(2,6) 139, W(2,7) 617, W(2,8) 1069, W(3,5) 241, W(4,6) 18061, W(5,5) 6011, W(6,5) 14173, W(5,6) 49391, W(6,6) 90067. None for W(5,3) below 200.

## Bounds below the records, within the budget

- W(4,6) >= 157211: Xu's recursion with `p = 139` and the W(2,6) witness, `139 * 1131` integers, plus 1 by greedy extension at the end. The record 157349 is `139 * 1132 + 1`, one more block of 139, so it seems to use a quotient sequence one longer than any 2-coloring avoiding 6-term progressions, probably by treating the last block specially.
- W(5,5) >= 88526: `blankenship-c-t-2018` with `p = 5` from W(4,5) >= 17706 (greedy extension added nothing). W(6,5) >= 88534 is the same coloring extended greedily with a sixth color. Records 98742 and 98755 (`komkov-2016`) are still unexplained (see below).
- W(5,3) >= 121: tabu search (min-conflicts with incremental scores, in C) found a 5-coloring of 120 integers avoiding 3-term progressions in a few hundred thousand moves, but none of 125 integers in 15 minutes or 130 in 2 minutes (stalling at a few dozen conflicts). Blankenship with `p = 3` gives only 79. The record 171 came from a SAT solver.

## Not yet reproduced

- `W(4,6) >= 157349` (`monroe-2022`), `W(5,5) >= 98742` and `W(6,5) >= 98755` (`komkov-2016`), `W(6,6) >= 1555550`: none fit `value - 2 = (k - 1) m p` with `r | p - 1`, or the product constructions above. Plain Rabung with `p = 31469` fails for `W(4,6)`.
- `W(5,3) >= 171`: Monroe says it was found by a SAT solver, not a Rabung coloring.
- Monroe's code and the primes his search found, but no colorings, are at https://github.com/hmonroe/vdw.
