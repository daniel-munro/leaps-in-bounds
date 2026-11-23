# Lebesgue's universal covering problem

Only Lean proofs are accepted for this family (see `certificates/blocked.yml` for why the current bounds aren't certified).

## Toward a certificate

- **Lower bounds.** Every lower bound so far minimizes the area of the convex hull of a few fixed sets of diameter 1 over their placements: a disk and an equilateral triangle (pal-1920, π/8 + √3/4), Reuleaux polygons with 3^k sides (elekes-1994), and a disk, triangle and regular pentagon (brass-sharifi-2005, 0.832; xie-2026, 0.833). Xie's records (356,816 parameter domains with outward-rounded interval bounds) are public at https://github.com/Sheldon-Anderson/lebesgue-universal-cover-new-lower-bound-certificate, but its replay verifier checks hashes, counts and pass fields, not the geometry. A checker that recomputed each domain's interval bound from the records would make a witness format possible, though it would still rest on Brass and Sharifi's normalization of the placements, which would need its own proof, and the statement here would need a checker change reviewed on its own.
- **Upper bounds.** Pál's cover (hexagon of width 1 minus two corners, 2 - 2/√3) is the natural first Lean target. A proof needs that every set of diameter at most 1 lies in a set of constant width 1 (Vrečica 1981), that such a set fits in the hexagon of width 1 in every orientation (Pál), and the 60° rotation argument for the cut corners. None of this is in Mathlib as of 2026-11.

## Searches

None recorded yet.
