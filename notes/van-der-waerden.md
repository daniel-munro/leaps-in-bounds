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

The first matching `s` worked each time, and the multiples of `p` always had a valid coloring. `W(3,11) >= 18603732` is `m = 1` with `p = 1860373` too. Its witness would compress to roughly 500 kB with xz (judging by 124 kB for `W(3,10)`), at the size limit, and the checker in `scripts/certificates/families/van_der_waerden.py` would take hours on it.

No plain Rabung prime (`m = 1`) gets close for 3 colors: the best for `W(3,5)` is `p = 241` (964 integers), and for `W(3,7)` it's `p = 7309` (43854).

## Product constructions

- `blankenship-c-t-2018`: for a prime `p <= k`, `W(r,k) > p (W(r - ceil(r/p), k) - 1)`. Integer `p q + j` gets the color of `q` in the smaller coloring, relabeled into a set of colors for residue `j`, so that no color is used for all residues. `W(6,3) >= 226` is this with `p = 3` from `W(4,3) >= 76`. `W(5,6) >= 786741` is `p = 5` from `W(4,6) >= 157349`, which has no witness here yet.
- Xu's recursion, `W(st,k) >= p (W(t,k) - 1) + 1` (`xu-2013`, Theorem 4; Monroe restates it with `>`): color `x` by the pair (Rabung `s`-coloring of `x mod p`, `t`-coloring of `floor(x / p)`). `W(4,7) >= 2284752` is `p = 617` with `W(2,7) >= 3704`.

## Checker budget and initial bounds

The checker in `scripts/certificates/families/van_der_waerden.py` does `k - 1` shifts and ANDs of an `n`-bit integer for each color and each difference, so its time grows like `r n^2` and doesn't depend on `k`: about 80 s of CPU for `r n^2 = 1.3 * 10^12` (`n` about 658k for 3 colors, 570k for 4, 510k for 5, 465k for 6). Witnesses of that size compress to 20 to 30 kB with xz, so time, not the size limit, is what binds. Every constant whose record is beyond this budget got an initial bound at the budget:

- Plain Rabung (`m = 1`), with the largest prime `p = 1 mod r` below `budget / (k - 1)` that passes the window filter (a few seconds each to find): W(3,11) p = 65809, W(4,8) 81401, W(4,9) 71257, W(4,10) 63337, W(4,11) 56993, W(5,7) 84751, W(5,8) 72661, W(5,9) 63691, W(5,10) 56611, W(5,11) 50971, W(6,7) 77569, W(6,8) 66463, W(6,9) 58171, W(6,10) 51691, W(6,11) 46507. The multiples of `p` can get any color, since the filter already breaks every progression with difference not divisible by `p`.
- Truncated products: W(5,6) >= 509901 is `blankenship-c-t-2018` with `p = 5` on the first 101980 integers of the W(4,6) witness (the whole witness would give 786051 but take about 3 minutes to check); W(6,6) >= 465373 is Xu's recursion with `p = 139` on the first 3348 integers of the W(3,6) witness (all of it gives the record 1555550).

## Hour budget (generators)

With generator witnesses, a check can take up to about an hour. Measured on an otherwise lightly loaded machine, the checker does about `r n^2 = 3 * 10^10` per second (130 s for `n = 991880`, `r = 4`), steady from `n = 300k` to `1M`; under heavy load from other jobs it was 2 to 3 times slower. The second round of bounds is sized to `r n^2 = 3.6 * 10^13`, about 20 minutes unloaded: `n` about 3.46M for 3 colors, 3.0M for 4, 2.68M for 5, 2.45M for 6.

- Plain Rabung (`m = 1`), as generators (`certificates/van-der-waerden/*.py`, one template with `R, K, P, G` filled in; under a second to run, versus 100 to 200 kB as `.txt.xz`). Each colors `0` to `(k - 1) p` with the multiples of `p` colored `0, 1, 2, ...`, so the value is `(k - 1) p + 2`. Primes, with primitive root: W(3,11) 345739 (7), W(4,9) 374909 (2), W(4,10) 333233 (3), W(4,11) 299993 (5), W(5,8) 383321 (3), W(5,9) 335341 (6), W(5,10) 298031 (13), W(5,11) 268291 (2), W(6,8) 349849 (7), W(6,9) 306169 (13), W(6,10) 272131 (2), W(6,11) 244939 (2). Each was the largest passing prime below the budget, found within a few seconds.
- The window filter fails more often as `p` grows: the expected number of bad windows is about `p r^(1 - k)`, so a prime passes with probability about `exp(-p r^(1 - k))`. At the budget this is hopeless for W(4,8) (about 26 bad windows expected), W(5,7) (29) and W(6,7) (9). Those use truncated products instead, as `.txt.xz` (5 to 11 kB): W(4,8) Xu with `p = 1069` (base 6) on the first 2806 integers of the W(2,8) witness; W(5,7) Blankenship with `p = 5` on the first 536656 integers of the W(4,7) witness; W(6,7) Xu with `p = 617` (base 3) on the first 3969 integers of the W(3,7) witness.
- Full products, as `.txt.xz`: W(5,6) >= 786079 is Blankenship with `p = 5` on the whole W(4,6) >= 157211 witness (786050 integers), then greedy extension by 25 integers at the end and 3 at the start. W(6,6) >= 1555551 is Xu with `p = 139` on the whole W(3,6) witness plus one integer: the next multiple of `p` can take a color whose `a` component (1) no other multiple of `p` has, one more than Xu's theorem gives (`W(6,6) >= 139 (W(3,6) - 1) + 1 = 1555550`, the record). The same holds for W(4,7) >= 2284753 (`617 * 3703 + 2`), one more than `xu-2013`'s 2284752. It may work for other Xu products too, but that's only checked for these two. Greedy extension found nothing more for either.
- Measured check times (wall clock, `verify_certificates.py --jobs 3`): on a machine with load average 100 to 150 from other jobs, 64 to 91 minutes for the first six at the budget (CPU time roughly double the unloaded estimate, from contention), 40 to 43 for the next three, and 19 to 22 minutes for the last six once the load dropped, close to the unloaded estimate of 20. W(5,6) 5 minutes, W(6,6) 30 minutes and W(4,7) 49 minutes, all under heavy load. So on a busy machine the budget is about an hour; don't go larger with this checker.
- Running several `verify_certificates.py` processes at once loses manifest entries: each reads `certificates/verified.yml` when it starts and writes the whole file when it ends, so the last to finish drops entries the others recorded in between. Run one at a time, with `--jobs`.
- In a truncated product the greedy extension at the cut end can go on for a whole block or more, since the base coloring continues; it isn't worth it when the size is capped by the budget anyway.
- A faster checker would unlock more: the records W(3,11) >= 18603732 (Rabung, `p = 1860373`) and the product bounds in the tens of millions need `r n^2` around `10^15`, beyond an hour of this checker (W(3,11) at the record would be about `10^15`, roughly 9 hours). The checker's work is inherent to checking an arbitrary coloring (about `n^2 / (k - 1)` progressions, done 64 at a time per color), so the big gains would need a witness format that describes the construction, such as Rabung `(p, g)` checked by the window filter in time linear in `p`, or a product checked from its base coloring.

Largest primes passing the Rabung filter (`m = 1`) for small cases: W(2,5) 37, W(2,6) 139, W(2,7) 617, W(2,8) 1069, W(3,5) 241, W(4,6) 18061, W(5,5) 6011, W(6,5) 14173, W(5,6) 49391, W(6,6) 90067. None for W(5,3) below 200.

## Bounds below the records, within the budget

- W(4,6) >= 157211: Xu's recursion with `p = 139` and the W(2,6) witness, `139 * 1131` integers, plus 1 by greedy extension at the end. The record 157349 is `139 * 1132 + 1`: Monroe's Table 2 gives it as `1,132 x 139`, using W(2,6) = 1132 where Xu's theorem uses W(2,6) - 1, so it looks like an arithmetic slip rather than a construction (Monroe's v6 gave 157210 instead). W(5,6) >= 786741 is `5 * 157348 + 1`, from it. See `literature/coverage.yml`.
- W(5,5) >= 88526: `blankenship-c-t-2018` with `p = 5` from W(4,5) >= 17706 (greedy extension added nothing). W(6,5) >= 88534 is the same coloring extended greedily with a sixth color. Records 98742 and 98755 (`komkov-2016`) are still unexplained (see below).
- W(5,3) >= 121: tabu search (min-conflicts with incremental scores, in C) found a 5-coloring of 120 integers avoiding 3-term progressions in a few hundred thousand moves, but none of 125 integers in 15 minutes or 130 in 2 minutes (stalling at a few dozen conflicts). Blankenship with `p = 3` gives only 79. The record 171 came from a SAT solver.

## Not yet reproduced

- `W(4,6) >= 157349` (`monroe-2022`), `W(5,5) >= 98742` and `W(6,5) >= 98755` (`komkov-2016`): none fit `value - 2 = (k - 1) m p` with `r | p - 1`, or the product constructions above. Plain Rabung with `p = 31469` fails for `W(4,6)`.
- `W(5,3) >= 171`: Monroe says it was found by a SAT solver, not a Rabung coloring.
- Monroe's code and the primes his search found, but no colorings, are at https://github.com/hmonroe/vdw.

## Literature review (2026-11-23)

- Read through: Rabung 1979 (table), Dransfield et al. 2003 and 2004, Herwig et al. 2007 (Tables 1, 3, 4), Heule's 2009 slides, the SAT@Delft page (2011), Rabung and Lotts 2012 (Table 1), Heule 2017 (Table 1), Blankenship, Cummings and Taranchuk (arXiv v1, Figure 1), Monroe arXiv:1603.03301 v1, v3 to v7 (Tables 1 and 2), Komkov viXra:1611.0385 v1 and v2 and arXiv:1701.05603 v1 to v5, Kouril 2012, OEIS A005346 and Wikipedia. Every bound for 2 to 6 colors and lengths 3 to 11 in them is in the history or superseded within the same source.
- W(5,3) > 125 was on the Kentucky group's web page by 2003-04-15 (Wayback 2003-05-07), citing their SAT 2003 paper, so it's now credited to that paper rather than the 2004 journal version. The page's other bounds (W(2,6) > 341, W(3,4) > 187, ...) are below Rabung's.
- Monroe's code (https://github.com/hmonroe/vdw) only searches Rabung primes, with and without zipping; `output.txt` holds the best prime per (colors, length), e.g. 18266 = 2 x 9133 (zipped) for W(4,6), Herwig's 91331. The Xu and Blankenship products in Tables 1 and 2 aren't computed by it, so it can't explain W(4,6) > 157348. v7's Table 2 leaves the W(4,6) method blank (v4 to v5 gave `1,132x139`, v6 gave 157,209).
- Komkov viXra v2 (2018) and arXiv v5 (2020) also give W(5,6) > 540170 and > 540197; both are below Monroe's W(5,6) > 786740 (2017), so they aren't rows. Komkov's arXiv v1 to v4 have only 7 or more colors.
- Rabung 1979's W(2,11) > 196811 was misreported (Rabung and Lotts 2012) and isn't recorded.
- Landman and Robertson's book (1st ed. 2004) has W(3,5) > 1209, which Herwig et al. and SAT@Delft call untraceable; it would fall between Rabung's 966 and Heule et al.'s 2174 if a source is found.
- Second pass: Stevens and Shantaram 1978 (received 1976-04-19) give only the 2-color values up to W(2,5) = 178. Beeler and O'Neil 1979 give W(4,3) = 76 and say the best previous bound was Rabung's W(4,3) > 75; their other new values are off-diagonal. Landman and Robertson's 2nd edition (2014) was only seen in its front and back matter: Table 2.2 (p. 43, values and lower bounds for w(k;r)) is in Chapter 2, which wasn't available. Its references for this table that are diagonal (Rabung, Rabung-Lotts, Herwig et al., Heule, Dransfield et al., Kouril, Kouril-Paul, Liang et al. 2012) are all read except Liang et al., which Monroe credits only for lengths 13 and up. Its reference list also has Kouril's 2006 PhD thesis, which may be the first source of W(2,6) = 1132.
- Third pass: Landman and Robertson's Table 2.2 read in both editions. The 1st edition (2004, p. 38) cites all its lower bounds to Rabung 1979 and mostly writes Rabung's `W > n` as `W >= n` (W(2,6) >= 696, W(3,4) >= 292, ...); its W(3,5) >= 1210 matches nothing in Rabung (W(3,5) > 965) and is the "untraceable" 1209 of Herwig et al., taken here as an error. The 2nd edition (2014, p. 43) cites Rabung and Heule's SAT@Delft page; every entry is already in the history (its W(5,6) >= 540025 is one below Heule's).
