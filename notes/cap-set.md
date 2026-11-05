# Cap sets

## Where the records are

- Exact values are known for n <= 6. The certificates for n = 7 and 8 are the published records: the affine part of Edel's 248-cap in PG(7,3) (`edel-bierbrauer-2001`), and FunSearch's 512-cap (`romera-paredes-et-al-2023`), from https://github.com/google-deepmind/funsearch/blob/main/cap_set/n8_size512.txt.
- Yves Edel's page, http://www.yvesedel.de/Matritzen/CAPs/CAPMatIndex.html, has explicit large caps in PG(n,3) for n up to 12, as check matrices whose columns are the points. A projective cap of size s with a hyperplane meeting it in h points gives an affine cap of size s - h. The page's last row of each matrix is a word of maximum weight, so the points with a nonzero last coordinate are already the largest affine part.
- `karapetyan-karapetyan-2026` summarizes the known values and bounds for AG(n,3) and gives lower bounds for some larger n (r(11) >= 5504, r(15) >= 124928).

## Searches

- Plain depth-first search finds optimal caps for n <= 4 instantly. The certificates for n = 5 and 6 are hyperplane sections of the n = 7 cap: the largest section of the 236-cap has 112 points, and the largest section of that has 45. The largest section of the 45-cap has only 18 points, so the 20-cap for n = 4 came from search.
- FunSearch reports finding the 512-cap in only 4 of 140 runs, and X-evolve (arXiv:2508.07932) matches it but doesn't beat it. Any new search for n = 8 should start from the 512-cap, not from scratch.

## Upper bounds

- `versluis-2017` (a bachelor's thesis) gives r(7) <= 291, r(8) <= 771, r(9) <= 2070 and r(10) <= 5619 by computer-assisted recursive counting. `thackeray-2022` (a preprint) proves that no 289-cap exists in AG(7,3), so r(7) <= 288. Neither has been checked against an independent source.
- The site only goes up to n = 8 so far, since no sourced lower bounds for n = 9 and 10 were found. Product constructions give some (for example 112 x 9 = 1008 for n = 9), but the records come from Edel's constructions and haven't been traced.
