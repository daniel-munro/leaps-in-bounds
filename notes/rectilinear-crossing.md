# Rectilinear crossing number

## Where the records are

- Oswin Aichholzer's Rectilinear Crossing Number project page at TU Graz (`aichholzer-crossing-page`) has the lower bounds and best known point sets (`best028.asc` and so on) for n <= 100. Its table was last modified 2015-05-26. The page refused connections on 2026-11-12; the bounds here were read from a Wayback Machine capture of 2022-02-14. The point set files themselves haven't been fetched, so they aren't certificates yet.
- `abrego-et-al-2011`, Section 6, lists lower bounds for 28 <= n <= 99 (on the pseudolinear crossing number, which is at most the rectilinear one). They match the page's lower bounds.
- `fabila-monroy-lopez-2014`, Table 1, improved the best point sets for many n from 46 to 99 by local search, and lists the previous best for each. The paper prints its 75-point set with 450492 crossings (the certificate for n = 75); its other sets are said to be on its arXiv page.

## Searches

All in C with 64-bit integer coordinates (128-bit orientation tests in the symmetric search), recounting only the 4-point subsets that contain a moved point.

- Simulated annealing that moves one point at a time to a random nearby integer point, with move sizes spread over six orders of magnitude, starting from points in three clusters at the corners of a triangle, with restarts from the best set every 200000 moves.
  - Reached the known value within seconds for n <= 23 and for n = 25, from each of three seeds.
  - Fell short within 5 to 15 minutes per run (best of 3 to 6 seeds): n = 24 by 1, n = 26 by 1 (5251), n = 27 by 4 until a longer run reached 6180, n = 28 by 3 against the best known 7234 (7237), and n = 30 by 8. It reached 8423 for n = 29, matching the best known.
  - Occasionally jumping a point next to another random point didn't help for n = 24.
- The same annealing restricted to point sets with 3-fold rotational symmetry (n = 3k, k orbits, rotated points rounded to integers at scale 10^9) reached the optimum for n = 24, 27 and 30 in 15 minutes for one or more of three seeds.
- Warm starts didn't help: starting from the n = 23 set plus a point for n = 24, or from the n = 27 and 29 sets minus a point for n = 26 and 28 (5263 and 7250 before annealing), ended no better than fresh runs.
- For n <= 12, the same annealing on a 61 x 61 grid reaches the optimum within seconds. The certificates for n <= 12 are the optimal sets, among 200 seeds, whose vertices and crossings are farthest apart, then hill-climbed to spread them further, so that they draw clearly.
- Not yet tried: the 3-fold symmetric search with a fixed point or orbit structure for n = 26 and 28 (n not divisible by 3), longer runs, or starting from the page's point sets.
