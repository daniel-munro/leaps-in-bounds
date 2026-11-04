# Snake-in-the-box and coil-in-the-box

Covers both `snake-in-the-box` and `coil-in-the-box`.

## Where the records are

- Tom Ace's records page, https://www.minortriad.com/snake/, keeps the current records for n <= 13 and a dated log of updates (in the page's HTML comments). Its witnesses are 0-based hex transition sequences from vertex 0, which is the certificate format, and a coil's sequence includes its closing edge.
- Math-AI-Caltech/Snake-in-the-Box on GitHub has the records and large banks of snakes and coils for n = 9 to 13 from `orland-et-al-2026`.
- `taylor-2026` constructs snakes for n = 14 to 20, but the site only goes up to n = 13 so far.
- Wikipedia's table lagged the records page by months in 2026.

## Searches

- Plain depth-first search, with transitions limited to at most one new coordinate beyond those used so far and the next vertex chosen to have the fewest free neighbors, finds optimal snakes and coils for n <= 6 in seconds. This is how the certificates for n <= 6 were found. For n = 7 it found nothing of length 50 (snake) or 48 (coil) within about 5 minutes. The n = 7 and larger certificates are the published records.
- Since mid-2025, records for n = 10 to 13 have moved every few weeks. The methods behind them are extending and rerouting existing records, priming searches with snakes from lower dimensions (`ace-2026a`), and "snakepit surgery" (`orland-et-al-2026`). Any new search should start from the current records, not from scratch.

## Upper bounds

- Exact values are known for n <= 8. For n >= 9 the site records no upper bounds yet.
- For a coil in Q_n with n >= 5, Huang's sensitivity theorem (Annals of Math. 190 (2019)) gives at most 2^(n-1) vertices, so c(n) <= 2^(n-1) and s(n) <= 2^(n-1) - 1.
- Older general bounds, such as those of Snevily (1994), Zémor (1997) and Lukito and van Zanten (2001), are stronger for some n. No one has yet evaluated them for n = 9 to 13 and checked them against the sources.
