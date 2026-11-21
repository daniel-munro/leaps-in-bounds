# Heilbronn triangle problem in a triangle

## Status

- Every lower bound for n = 3 to 36 is certified from the configurations in Stead's tables (`stead-heilbronn-triangle`), in the triangle (0, 0), (1, 0), (0, 1), with areas doubled to make them fractions of the triangle's area. For n = 4, 7 and 9 the 30-digit decimals there approximate simple fractions (the n = 9 configuration is on a 1/56 grid), and the certificates use the fractions, so they reach 1/3, 7/72 and 43/784 exactly.
- See `notes/heilbronn-square.md` for the checker and rounding.

## Ideas

- n = 8 has the upper bound 35555/2^19 < 0.067816 (Chen, Zeng and Zhou 2013, by a subdivision search like De Comité and Delahaye's). It is conjectured to be twice the real root of a septic (Chen, Zeng and Zhou), certified numerically by Sudermann-Merx (arXiv:2607.15021) and by Ethan Hendren's AI-assisted branch and bound (November 2026). An independent check of Hendren's proof could support an attested upper bound.
