# Modifications

Changes made to the original source, as required by section 4(b) of the Apache License 2.0.

## `StrongPNT.lean` (from `PrimeNumberTheoremAnd/StrongPNT.lean` at `a4fb698`)

- Only lines 34–1230 are taken: the general complex analysis from
  `AnalyticOn.norm_le_of_norm_le_on_sphere` to `FinalBound`. The file header, the imports, the
  ζ-specific notation, and everything from line 1231 on (the `HasProd.nnnorm` API and all
  results about the Riemann zeta function) are omitted.
- A header comment naming the source, the commit and the license is added (the original file has
  no copyright header), and a module docstring.
- The imports of `Architect` and `PrimeNumberTheoremAnd.MediumPNT` are replaced by the Mathlib
  modules the excerpt uses.
- Everything is put in `namespace RiemannMasullo.External.PrimeNumberTheoremAnd`, so that no name
  collides with Mathlib or this project. Declaration names are unchanged.
- The `@[blueprint …]` attributes (from the `Architect` blueprint tool, not available here) are
  removed. Each attribute's `statement` text becomes the declaration's docstring; the `title`,
  `proof` and `latexEnv` fields are dropped. The `blueprint_comment /-- … -/` commands become
  `/-! … -/` module comments with the same text.
- Port to Lean v4.36.0 and this project's Mathlib (`fc4f59e`): in the proof of
  `LogOfAnalyticFunction`, `enorm_eq_iff_norm_eq` and `enorm` (deprecated) are replaced by
  `eNorm_eq_iff_norm_eq` and `eNorm`. No other proof is changed.
- Runs of more than two blank lines are reduced to two.
- The Masullo workspace port uses equality of norms directly and the available
  `Finset.prod_le_prod` and `logDeriv_prod` declarations.

## `WienerIkehara.lean` (from Mathlib 4.36.0 at `fc4f59e`)

- The original copyright and author notice is retained. Mathlib's file is itself an adaptation from PrimeNumberTheoremAnd.
- The import of Mathlib's compact-support density result uses the workspace's compact Schwartz approximation. The old module interface requires ordinary imports.
- The port supplies the small comparison, substitution, and cutoff lemmas missing from the older Mathlib checkout and makes several calculus steps explicit for its APIs. The Wiener–Ikehara hypotheses and conclusions are unchanged.
