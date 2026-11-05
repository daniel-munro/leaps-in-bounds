# No-three-in-line problem

## Where the records are

- Achim Flammenkamp's page, http://wwwhomes.uni-bielefeld.de/achim/no3in/readme.html, has dated announcements of every new grid size since 2025 and a database of known configurations, which its "Show" form (a POST to `/cgi-bin/cgiwrap/achim/script_lookup` with `size` and `index`) prints as a grid of `o` and `.`. The certificates for n = 65 to 78 come from it.
- The page's coded configurations (`data_1997/known_solutions`, and the encoding described on the page) give a symmetry character, then the two chosen columns of each row in turn. That list has solutions for every n <= 46 and for 48, 50 and 52.
- Prellberg's file, https://oeis.org/A272651/a272651_15.txt, lists solutions for n = 47 to 64 as (x, y) coordinates.

## Searches

- Recent records all have a symmetry: rot4 (quarter-turn) for even n, and rct4 (quarter-turn except on one long diagonal) for odd n. They came from constraint satisfaction (`prellberg-2025`), GPU enumeration, and a SAT solver (`heule-2026-06-17` and later).
- As of 2026-11-05 no 2n-point solution is known for n = 75 or 77, or for any n >= 79. The certificates for n = 75 and 77 just reuse the solutions for n = 74 and 76 (148 and 152 points). Placing those solutions in a corner of the larger grid, in all four ways, leaves no empty grid point that can be added without making three in a line.

## Upper bounds

- The only upper bound recorded is the trivial 2n, since each row holds at most two points. It matches the lower bound for every n <= 74 and for n = 76 and 78. For n = 75, 77 and n >= 79, no better upper bound is known. Proving D(n) < 2n for a specific n would take an exhaustive search over all configurations, which so far has only been done within single symmetry classes.
