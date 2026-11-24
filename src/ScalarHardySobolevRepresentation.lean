import MellinPoissonBoundary
import ScalarFractionalCutoff

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

/-- On a nondegenerate compact base the actual holomorphic transform
determines the full weighted class, even from one interior line. -/
theorem scalarMellinMoment_injective_line {a b s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Ioo a b) :
    Injective (fun (f : StripSobolev a b s) (y : ℝ) =>
      scalarMellinMoment f 0 (⟨t, 2 * Real.pi * y⟩ : ℂ)) := by
  intro f g hfg
  let hab := (ht.1.trans ht.2).le
  let ht' := Ioo_subset_Icc_self ht
  have htrace : scalarFractionalTrace hab ht' s f = scalarFractionalTrace hab ht' s g := by
    apply mellinFrequencyValues_injective hs
    apply Lp.ext
    refine (scalarFractionalTrace_interior_values hs ht f).trans ?_
    dsimp only at hfg
    rw [hfg]
    exact (scalarFractionalTrace_interior_values hs ht g).symm
  apply Lp.ext
  apply (amplitudeMeasure_absolutelyContinuous volume (stripSobolevAmplitude a b s)).ae_le
  filter_upwards [scalarFractionalTrace_ae hab ht' s f, scalarFractionalTrace_ae hab ht' s g]
    with x hf hg
  rw [htrace] at hf
  exact smul_right_injective ℂ (Real.exp_pos (t * x)).ne' (hf.symm.trans hg)

private theorem scalarHalfLineMoment_injective {b s : ℝ} (hs : 0 ≤ s)
    {f g : StripSobolev b b s} {F : StripSobolev b b s → ℝ → ℝ → ℂ}
    (hf : ∀ᵐ y ∂volume, Tendsto (fun t => F f t y) (𝓝[>] (0 : ℝ))
      (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s f) y)))
    (hg : ∀ᵐ y ∂volume, Tendsto (fun t => F g t y) (𝓝[>] (0 : ℝ))
      (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s g) y)))
    (he : ∀ t > 0, ∀ y, F f t y = F g t y) : f = g := by
  apply (fractionalMellinLine b s).injective
  apply mellinFrequencyValues_injective hs
  apply Lp.ext
  filter_upwards [hf, hg] with y hf hg
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  exact tendsto_nhds_unique (hf.congr' (hpos.mono fun t ht => he t ht y)) hg

theorem scalarRightHalfLineMoment_injective {b s : ℝ} (hs : 0 ≤ s)
    {f g : StripSobolev b b s}
    (hf : ∀ᵐ x ∂volume, 0 < x → f x = 0) (hg : ∀ᵐ x ∂volume, 0 < x → g x = 0)
    (he : ∀ z : ℂ, b < z.re → scalarMellinMoment f 0 z = scalarMellinMoment g 0 z) : f = g :=
  scalarHalfLineMoment_injective (F := fun q t y =>
    scalarMellinMoment q 0 (⟨b + t, 2 * Real.pi * y⟩ : ℂ)) hs
    (scalarRightHalfLineTrace_boundary_ae hs f hf) (scalarRightHalfLineTrace_boundary_ae hs g hg)
    (fun t ht y => he ⟨b + t, 2 * Real.pi * y⟩ (by change b < b + t; linarith))

theorem scalarLeftHalfLineMoment_injective {b s : ℝ} (hs : 0 ≤ s)
    {f g : StripSobolev b b s}
    (hf : ∀ᵐ x ∂volume, x < 0 → f x = 0) (hg : ∀ᵐ x ∂volume, x < 0 → g x = 0)
    (he : ∀ z : ℂ, z.re < b → scalarMellinMoment f 0 z = scalarMellinMoment g 0 z) : f = g :=
  scalarHalfLineMoment_injective (F := fun q t y =>
    scalarMellinMoment q 0 (⟨b + -t, 2 * Real.pi * y⟩ : ℂ)) hs
    (scalarLeftHalfLineTrace_boundary_ae hs f hf) (scalarLeftHalfLineTrace_boundary_ae hs g hg)
    (fun t ht y => he ⟨b + -t, 2 * Real.pi * y⟩ (by change b + -t < b; linarith))

/-- The actual original tests are dense in the compatible compact endpoint
completion, for any test interval containing the endpoints. -/
theorem scalarCompactMellinTest_dense {J : Set ℝ} (a b : J) (hab : (a : ℝ) ≤ b) (s : ℝ) :
    DenseRange (fun f : PositiveRealExponentialDecay J =>
      scalarFractionalIntervalEquiv hab s (stripSobolevTest J a b s f)) := by
  let E := scalarFractionalIntervalEquiv hab s
  exact E.surjective.denseRange.comp (stripSobolevTest_denseRange J a b s) E.continuous

private theorem scalarFractionalCutoff_congr_ae {a b s : ℝ} (hab : a ≤ b) {U V : Set ℝ}
    (hUV : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ U ↔ x ∈ V) :
    scalarFractionalCutoff hab s U = scalarFractionalCutoff hab s V := by
  ext g
  obtain ⟨f, rfl⟩ := (scalarFractionalIntervalEquiv hab s).surjective g
  rw [scalarFractionalCutoff_mem_iff, scalarFractionalCutoff_mem_iff]
  apply eventually_congr
  filter_upwards [hUV] with x hx
  simp only [hx]

/-- The original finite-norm scalar tests on the right half-line complete
to the compatible endpoint model of the nonpositive logarithmic support. -/
theorem scalarRightHalfLineMellinTest_closure (J : Set ℝ) (b : J) (s : ℝ) :
    closure {z | ∃ f : PositiveRealExponentialDecay J,
      hardySobolevIntervalENorm volume id (Ici (b : ℝ)) s f.val ≠ ⊤ ∧
      scalarFractionalIntervalEquiv le_rfl s (stripSobolevTest J b b s f) = z} =
      (scalarFractionalCutoff (a := (b : ℝ)) le_rfl s (Iio 0) : Set (scalarFractionalInterval b b le_rfl s)) := by
  simp_rw [(scalarFractional_halfLineTestSupport J b s _).1]
  exact (scalarFractional_cutoffTestClosure_of_ae J b b le_rfl s isOpen_Iio
    Iio_subset_Iic_self scalarFractional_halfLineRays.1).trans
      (congrArg (fun U : Submodule ℂ (scalarFractionalInterval b b le_rfl s) =>
        (U : Set (scalarFractionalInterval b b le_rfl s)))
        (scalarFractionalCutoff_congr_ae (a := (b : ℝ)) (s := s) le_rfl scalarFractional_halfLineRays.1))

/-- The original finite-norm scalar tests on the left half-line complete
to the compatible endpoint model of the nonnegative logarithmic support. -/
theorem scalarLeftHalfLineMellinTest_closure (J : Set ℝ) (b : J) (s : ℝ) :
    closure {z | ∃ f : PositiveRealExponentialDecay J,
      hardySobolevIntervalENorm volume id (Iic (b : ℝ)) s f.val ≠ ⊤ ∧
      scalarFractionalIntervalEquiv le_rfl s (stripSobolevTest J b b s f) = z} =
      (scalarFractionalCutoff (a := (b : ℝ)) le_rfl s (Ioi 0) : Set (scalarFractionalInterval b b le_rfl s)) := by
  simp_rw [(scalarFractional_halfLineTestSupport J b s _).2]
  exact (scalarFractional_cutoffTestClosure_of_ae J b b le_rfl s isOpen_Ioi
    Ioi_subset_Ici_self scalarFractional_halfLineRays.2).trans
      (congrArg (fun U : Submodule ℂ (scalarFractionalInterval b b le_rfl s) =>
        (U : Set (scalarFractionalInterval b b le_rfl s)))
        (scalarFractionalCutoff_congr_ae (a := (b : ℝ)) (s := s) le_rfl scalarFractional_halfLineRays.2))

end
end Masullo
