# Masullo

This repository holds an autoformalization of Alessandro Masullo's *Music of the Primes*.

It formalizes 564 out of 591 numbered resuls in the paper (95%) with 27 still open.

Of the 564 results, 329 were formalized as-stated or under the paper's intended conventions,
and 235 required a repaired statement.

### Tracking gaps

[GAPS.MD](GAPS.MD) tracks manuscript claims that still need a proof or a corrected statement.
When Lean verifies a repair, [OLD_GAPS.MD](OLD_GAPS.MD) records what failed in the manuscript,
what the repair proves, and where to find the Lean proof. If a repair covers only part of a
result, the remaining obligation stays in [GAPS.MD](GAPS.MD).

### Repository layout

- [src/](src/) contains the Lean library and vendored code. Use it as the Lean source root.
- [audits/](audits/) contains standalone verification files. Some require the external project at the revision recorded in the file.
- [PROGRESS.md](PROGRESS.md#checking-the-current-files) gives the build instructions and tracks manuscript coverage.

### Attribution

Significant credit goes to [Neal Patel](github.com/thatnealpatel/grh) and [Ryan McCorvie](github.com/mccorvie/riemann-masullo)
whose alternative auto-formalization projects were periodically drawn on by my formalizer.

### Pausing

I've decided to stop formalizing this paper, leaving the exact pausepoint in HANDOFF.MD.

The reason for pausing is that the paper has major gaps that require novel research, most significantly Theorem 12.5.1.1,
which is at least as difficult as proving the (non-generalized) Riemann Hypothesis. I don't see a point in taking a stab at
that on my own, so I'm releasing my formalization in the hopes that it's useful in the margins to another project.

At a little over 320K lines of Lean output in this repository, this was a fun exercise in running my verifier.
