import ElementarySchwartzCutoffs
import BruhatSobolevConvolution
import BruhatCompactSupport
import ModulatedSobolevApproximation

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Twisting by any real power of the modulus preserves Bruhat smoothness. -/
theorem bruhatSmooth_realModulation_smul (m : G →ₜ* Multiplicative ℝ)
    (b : ℝ) {f : G → ℂ} (hf : f ∈ bruhatSmoothSubmodule (G := G)) :
    (fun g => Real.exp (b * (m g).toAdd) • f g) ∈ bruhatSmoothSubmodule (G := G) := by
  intro s
  obtain ⟨P, hP, hPd⟩ := hf s
  refine ⟨P, ?_, fun Q hk q => ?_⟩
  · intro k x
    change Real.exp (b * (m (k.val * x)).toAdd) • f (k.val * x) =
      Real.exp (b * (m x).toAdd) • f x
    rw [map_mul, P.modulation_eq_one_on_kernel m k, one_mul, hP k x]
  obtain ⟨h, hh, hd⟩ := hPd Q hk q
  let A := ElementaryLCAModel q.realDim q.torusDim q.latticeRank q.finiteFactor
  let M := (Q.descendHom m (Q.modulation_eq_one_on_kernel m)).comp
    (q.equiv.symm : Multiplicative A →ₜ* Q.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  refine ⟨fun y => Real.exp (b * l y) • h y, fun x => ?_, fun a z => ?_⟩
  · have he : l (Q.stageCoordinates q x).toAdd = (m x.val).toAdd := by
      change ((Q.descendHom m (Q.modulation_eq_one_on_kernel m))
        (q.equiv.symm (q.equiv (QuotientGroup.mk x)))).toAdd = _
      rw [q.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
    change Real.exp (b * l (Q.stageCoordinates q x).toAdd) • h (Q.stageCoordinates q x).toAdd =
      Real.exp (b * (m x.val).toAdd) • f x.val
    rw [he, hh]
  · let X := EuclideanSpace ℝ (Fin q.realDim) × EuclideanSpace ℝ (Fin q.torusDim)
    let H := l.comp (elementaryCoverHom : X →+ A)
    have hH : Continuous H := hl.comp elementaryCoverHom_continuous
    let H₀ := H.toRealLinearMap hH
    let L : X →L[ℝ] ℝ := ⟨H₀, H₀.continuous_of_finiteDimensional⟩
    have he : (fun u : X => l (elementaryCover u a z)) =
        fun u => L u + l (elementaryCover (0 : X) a z) := by
      funext u
      have he := elementaryCover_add (0 : X) u a z
      rw [zero_add] at he
      rw [he, map_add, add_comm]
      rfl
    change ContDiff ℝ s (fun u : X => Real.exp (b * l (elementaryCover u a z)) •
      h (elementaryCover u a z))
    have hL : ContDiff ℝ s (fun u : X => l (elementaryCover u a z)) :=
      he.symm ▸ (L.contDiff.add contDiff_const)
    exact ((contDiff_const.mul hL).exp).smul (hd a z)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem hasCompactSupport_modulation_smul (m : G →ₜ* Multiplicative ℝ)
    (b : ℝ) {f : G → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun g => Real.exp (b * (m g).toAdd) • f g) := by
  apply hc.mono
  intro g hg h0
  apply hg
  change Real.exp (b * (m g).toAdd) • f g = 0
  rw [h0, smul_zero]

/-- Every compact Bruhat test belongs to the Schwartz–Bruhat chart at every
singleton abscissa. -/
theorem twist_mem_bruhatSchwartz_of_smooth_compactSupport (m : G →ₜ* Multiplicative ℝ)
    (b : ℝ) {f : G → ℂ} (hf : f ∈ bruhatSmoothSubmodule (G := G)) (hc : HasCompactSupport f) :
    (fun g => Real.exp (b * (m g).toAdd) • f g) ∈ bruhatSchwartzSubmodule (G := G) :=
  bruhatSchwartz_mem_of_smooth_compactSupport (bruhatSmooth_realModulation_smul m b hf)
    (hasCompactSupport_modulation_smul m b hc)

set_option maxHeartbeats 800000 in
/-- Cutoffs of the proper logarithmic coordinate approximate each Schwartz–Bruhat
function within a single elementary stage. -/
theorem exists_bruhatSchwartz_logCutoff_sequence (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (f : BruhatSchwartz G) :
    ∃ u : ℕ → BruhatSchwartz G, Tendsto u atTop (𝓝 f) ∧
      (∀ n g, (u n).val g = truncationMultiplier n (modulatedLog m g) * f.val g) ∧
      ∀ n, HasCompactSupport (u n).val := by
  obtain ⟨P, z, he⟩ := f.property
  let A := ElementaryLCAModel P.2.realDim P.2.torusDim P.2.latticeRank P.2.finiteFactor
  let M := (P.1.descendHom m (P.1.modulation_eq_one_on_kernel m)).comp
    (P.2.equiv.symm : Multiplicative A →ₜ* P.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  have h := @exists_elementarySchwartz_logCutoff_sequence P.2.realDim P.2.torusDim P.2.latticeRank
    P.2.finiteFactor P.2.finiteGroup P.2.finiteTopology P.2.finiteDiscrete (Finite.of_fintype _) l hl z
  let u : ℕ → P.Space := h.choose
  have hu : Tendsto u atTop (𝓝 z) := h.choose_spec.1
  have hu_eq := h.choose_spec.2
  have hP := locallyConvexFinal_stage_continuous (fun P : BruhatSchwartzStage G => P.inclusion) P
  have hz : P.inclusion z = f := Subtype.ext he
  have ht : Tendsto (fun n => P.inclusion (u n)) atTop (𝓝 f) := hz ▸ (hP.tendsto z).comp hu
  have hval (n : ℕ) (g : G) :
      (P.inclusion (u n)).val g = truncationMultiplier n (modulatedLog m g) * f.val g := by
    change P.realize (u n) g = _
    rw [← he]
    by_cases hg : g ∈ P.1.upper.val
    · let x : P.1.upper.val := ⟨g, hg⟩
      let y := (P.1.stageCoordinates P.2 x).toAdd
      have hy : l y = modulatedLog m g := by
        change ((P.1.descendHom m (P.1.modulation_eq_one_on_kernel m))
          (P.2.equiv.symm (P.2.equiv (QuotientGroup.mk x)))).toAdd = _
        rw [P.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
        rfl
      rw [show P.realize (u n) g = u n y from P.1.realizeSchwartz_apply_of_mem P.2 (u n) x,
        show P.realize z g = z y from P.1.realizeSchwartz_apply_of_mem P.2 z x, hu_eq n y, hy]
    · rw [P.1.realizeSchwartz_apply_of_not_mem P.2 (u n) g hg,
        P.1.realizeSchwartz_apply_of_not_mem P.2 z g hg, mul_zero]
  refine ⟨fun n => P.inclusion (u n), ht, hval, fun n => ?_⟩
  let R := 2 * ((n : ℝ) + 1)
  let K := modulatedLog m ⁻¹' Icc (-R) R
  have hc : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
  have hp : IsProperMap (modulatedLog m) := hm
  refine HasCompactSupport.intro' (hp.isCompact_preimage isCompact_Icc) (isClosed_Icc.preimage hc)
    (K := K) fun g hgK => ?_
  have hcR : R < |modulatedLog m g| := by
    apply lt_of_not_ge
    intro habs
    exact hgK (abs_le.mp habs)
  rw [hval n g, truncationMultiplier_zero n hcR, zero_mul]

theorem dense_bruhatSchwartz_compactSupport (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) :
    Dense {f : BruhatSchwartz G | HasCompactSupport f.val} := by
  intro f
  obtain ⟨u, hu, _, hc⟩ := exists_bruhatSchwartz_logCutoff_sequence m hm f
  exact mem_closure_of_tendsto hu (.of_forall hc)

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ)

/-- Compactly supported kernels determine the continuous singleton-strip
convolution action in the abscissa-twisted chart. -/
theorem existsUnique_bruhatSobolevAction_of_compactSupport (hm : IsProperMap m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    ∃! A : BruhatSchwartz G →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
      ∀ f : BruhatSchwartz G, HasCompactSupport f.val → ∀ u,
        A f u = ∫ g, (Real.exp (-(b * (m g).toAdd)) • f.val g) •
          hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs g u ∂μ := by
  let B := bruhatSobolevZeroLineAction μ m hm hms s hs
  have hB := bruhatSobolevZeroLineAction_twisted_formula μ m hm hms b s hs
  refine ⟨B, fun f _ u => hB f u, fun A hA => ?_⟩
  ext1 f
  have he : IsClosed {f | A f = B f} := isClosed_eq A.continuous B.continuous
  apply (closure_minimal (t := {f | A f = B f}) ?_ he) (dense_bruhatSchwartz_compactSupport m hm f)
  intro f hf
  exact ContinuousLinearMap.ext fun u => (hA f hf u).trans (hB f u).symm

/-- Corrected Lemma 9.3.2.1. The domain is the Schwartz–Bruhat chart at
the chosen abscissa. The unique action on compact tests admits a bounded
sequence of compact-spectrum kernels converging strongly to the identity. -/
theorem existsUnique_bruhatSobolevAction_with_approximation
    (hm : IsProperMap m) (hms : Surjective m) (b s : ℝ) (hs : 0 ≤ s) :
    ∃! A : BruhatSchwartz G →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
      (∀ (f : G → ℂ) (hf : f ∈ bruhatSmoothSubmodule (G := G)) (hc : HasCompactSupport f) u,
        A ⟨_, twist_mem_bruhatSchwartz_of_smooth_compactSupport m b hf hc⟩ u =
          ∫ g, f g • hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs g u ∂μ) ∧
      ∃ ψ : ℕ → BruhatSchwartz G,
        (∀ n, (fun g => Real.exp (-(b * (m g).toAdd)) • (ψ n).val g) ∈
          bruhatSmoothSubmodule (G := G)) ∧
        (∀ n, HasCompactSupport (lcaFourier μ (ψ n).val)) ∧
        (∀ n, ((PontryaginDual.map (modulatedKernelInclusion m)) ''
          tsupport (lcaFourier μ (ψ n).val)).Finite) ∧
        (∀ n, ‖A (ψ n)‖ ≤ 2) ∧ ∀ u, Tendsto (fun n => A (ψ n) u) atTop (𝓝 u) := by
  let B := bruhatSobolevZeroLineAction μ m hm hms s hs
  have hformula := bruhatSobolevZeroLineAction_twisted_formula μ m hm hms b s hs
  have hcancel (t : ℝ) (z : ℂ) : Real.exp (-t) • (Real.exp t • z) = z := by
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · intro f hf hc u
    rw [hformula]
    apply integral_congr_ae
    exact .of_forall fun g => congrArg
      (fun z : ℂ => z • hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs g u)
      (hcancel (b * (m g).toAdd) (f g))
  · obtain ⟨φ, _, hφ, hF, _, hi, hw, hnorm, ht⟩ := exists_zeroLineSobolev_approximation μ m hm hms s hs
    letI : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp
      (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
    let ψ (n : ℕ) : BruhatSchwartz G := ⟨φ n, hφ n⟩
    have he (n : ℕ) : B (ψ n) =
        singletonSobolevConvolution μ m 0 s hs (hi n).aestronglyMeasurable (hw n) := by
      ext u : 1
      rw [bruhatSobolevZeroLineAction_apply, singletonSobolevConvolution_apply]
    refine ⟨ψ, fun n => ?_, hF, fun n => ?_, ?_, ?_⟩
    · simpa only [neg_mul] using bruhatSmooth_realModulation_smul m (-b) (bruhatSchwartz_le_smooth (hφ n))
    · exact isCompact_iff_finite.mp
        ((hF n).image (PontryaginDual.map (modulatedKernelInclusion m)).continuous)
    · intro n
      rw [he]
      exact hnorm n
    · intro u
      simpa only [he] using ht u
  · intro A hA
    have hB := existsUnique_bruhatSobolevAction_of_compactSupport μ m hm hms b s hs
    apply hB.unique _ (fun f _ u => hformula f u)
    intro f hf u
    let f₀ (g : G) := Real.exp (-b * (m g).toAdd) • f.val g
    have hf₀ : f₀ ∈ bruhatSmoothSubmodule (G := G) :=
      bruhatSmooth_realModulation_smul m (-b) (bruhatSchwartz_le_smooth f.property)
    have hc₀ : HasCompactSupport f₀ := hasCompactSupport_modulation_smul m (-b) hf
    have he : (⟨_, twist_mem_bruhatSchwartz_of_smooth_compactSupport m b hf₀ hc₀⟩ :
        BruhatSchwartz G) = f := by
      apply Subtype.ext
      funext g
      change Real.exp (b * (m g).toAdd) • (Real.exp (-b * (m g).toAdd) • f.val g) = f.val g
      simpa only [neg_mul, neg_neg] using hcancel (-(b * (m g).toAdd)) (f.val g)
    have h := hA.1 f₀ hf₀ hc₀ u
    rw [he] at h
    simpa only [f₀, neg_mul] using h

end

end Masullo
