# Masullo

This repository holds an autoformalization of Alessandro Masullo's *Music of the Primes*.

It formalizes 564 out of 591 numbered resuls in the paper (95%) with 27 still open.

Of the 564 results, 329 were formalized as-stated or under the paper's intended conventions,
and 235 required a repaired statement.

### Attribution

Significant credit goes to [Neal Patel](github.com/thatnealpatel/grh) and [Ryan McCorvie](github.com/mccorvie/riemann-masullo)
whose alternative auto-formalization projects were periodically drawn on by my formalizer.

### Pausing

I've decided to stop formalizing this paper, leaving the exact pausepoint in HANDOFF.MD.

The reason for pausing is that the paper has major gaps that require novel research, most significantly Theorem 12.5.1.1,
which is at least as difficult as proving the (non-generalized) Riemann Hypothesis. I don't see a point in taking a stab at
that on my own, so I'm releasing my formalization in the hopes that it's useful in the margins to another project.

At a little over 320K lines of Lean output in this repository, this was a fun exercise in running my verifier.
