# Heilbronn triangle problem in a square

## Status

- Every lower bound for n = 3 to 36 is certified from the configurations in Stead's tables (`stead-heilbronn-square`), whose points.txt files give exact decimal coordinates. The least area of those coordinates, computed exactly, matches the tables' value for every n. For n = 11 and 16 the decimals approximate simple fractions (Goldberg's 1/27 grid and Beyleveld's 7/341 configuration), and the certificates use the fractions, so they reach the exact values.
- Optimal configurations have irrational coordinates, so other certificates give the least area of the decimal coordinates rounded down to ten significant digits.
- The checker computes all n choose 3 determinants in exact rational arithmetic: n = 36 takes well under a second, so n in the hundreds would be fine too.
- Upper bounds need Lean proofs (see `certificates/blocked.yml`). H(3) = H(4) = 1/2 is the easiest target: every triangle in the unit square has area at most 1/2.

## Ideas

- Stead's tables are being improved quickly (many records from August to November 2026, several by AI-assisted searches), so check them for new records before searching. The values there for n = 61, 65 and 75 are below those for n + 1, which can't be optimal, since deleting a point never decreases the least area: those n are easy improvements by deleting a point from the n + 1 record, if the family is extended past 36.
- Tie-system polishing (solving the equations that make the smallest triangles equal, to high precision) is what the current records use to squeeze out the last digits.
