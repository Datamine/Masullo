import HardySobolevRightPaleyWiener
import HardySobolevCompactTests
import HardySobolevBoundary

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

private abbrev LeftPlane (b : ℝ) := Complex.re ⁻¹' Iio b
private abbrev Cutoff (b : ℝ) (N : ℕ) (U : Set ℝ) :=
  supportedSobolevCompletion b b (2 * (N : ℝ)) U
private abbrev Line (b : ℝ) (N : ℕ) (U : Set ℝ) := supportedMellinLineCompletion b N U

/-- The canonical holomorphic realization of a lower-cutoff Mellin trace. -/
def lowerCutoffMellinLinear (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    Cutoff b N (Ioi c) →ₗ[ℂ] (LeftPlane b → ℂ) where
  toFun u z := cutoffMellinIntegral u.val 0 z.val
  map_add' u v := by
    funext z
    obtain ⟨L, hL⟩ := cutoffSobolev_mellinMoment_functional
      (a := b) (s := 2 * (N : ℝ)) hc (by positivity) (z := z.val) z.property 0
    simpa only [Pi.add_apply, cutoffMellinIntegral, (hL _).2] using L.map_add u v
  map_smul' c' u := by
    funext z
    obtain ⟨L, hL⟩ := cutoffSobolev_mellinMoment_functional
      (a := b) (s := 2 * (N : ℝ)) hc (by positivity) (z := z.val) z.property 0
    simpa only [Pi.smul_apply, RingHom.id_apply, cutoffMellinIntegral, (hL _).2] using L.map_smul c' u

theorem lowerCutoffMellinLinear_injective (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    Injective (lowerCutoffMellinLinear b N c hc) := by
  let r := b - 1
  have hr : r < b := by dsimp [r]; linarith
  intro u v huv
  apply cutoffMellinIntegral_line_injective hc (by positivity) hr
  funext y
  let z : LeftPlane b := ⟨(r : ℂ) + (y : ℂ) * Complex.I, by simpa [Complex.mul_re] using hr⟩
  exact congrFun huv z

private theorem compactCutoffMellin_integrable (b : ℝ) (N : ℕ) (c : ℝ)
    (u : Cutoff b N (Ioo c 0)) (z : ℂ) :
    Integrable (fun x => u.val x * mellinEvaluationKernel 0 z x) := by
  have h := (boundedStripSobolev_mellin_entire_bound b b _ c u).1 z
  have he : (fun x => u.val x * mellinEvaluationKernel 0 z x) = compactMellinKernel u.val z := by
    funext x
    simp only [mellinEvaluationKernel, pow_zero, mul_one, compactMellinKernel]
  rw [he]
  exact h

/-- The canonical entire realization of a compact-cutoff Mellin trace. -/
def compactCutoffMellinLinear (b : ℝ) (N : ℕ) (c : ℝ) :
    Cutoff b N (Ioo c 0) →ₗ[ℂ] (ℂ → ℂ) where
  toFun u z := cutoffMellinIntegral u.val 0 z
  map_add' u v := by
    funext z
    change cutoffMellinIntegral (u + v).val 0 z = cutoffMellinIntegral u.val 0 z + cutoffMellinIntegral v.val 0 z
    unfold cutoffMellinIntegral
    rw [← integral_add (compactCutoffMellin_integrable b N c u z) (compactCutoffMellin_integrable b N c v z)]
    have hAC := absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous b b (2 * (N : ℝ))).measurable
      (stripSobolevAmplitude_pos b b (2 * (N : ℝ)))
    apply integral_congr_ae
    filter_upwards [hAC.ae_le (Lp.coeFn_add u.val v.val)] with x hx
    change (u + v).val x = u.val x + v.val x at hx
    change (u + v).val x * _ = u.val x * _ + v.val x * _
    rw [hx, add_mul]
  map_smul' d u := by
    funext z
    change cutoffMellinIntegral (d • u).val 0 z = d • cutoffMellinIntegral u.val 0 z
    unfold cutoffMellinIntegral
    rw [← integral_smul]
    have hAC := absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous b b (2 * (N : ℝ))).measurable
      (stripSobolevAmplitude_pos b b (2 * (N : ℝ)))
    apply integral_congr_ae
    filter_upwards [hAC.ae_le (Lp.coeFn_smul d u.val)] with x hx
    change (d • u).val x = d • u.val x at hx
    change (d • u).val x * _ = d • (u.val x * _)
    rw [hx, smul_mul_assoc]

theorem compactCutoffMellinLinear_injective (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    Injective (compactCutoffMellinLinear b N c) := by
  let i : Cutoff b N (Ioo c 0) → Cutoff b N (Ioi c) := fun u =>
    ⟨u.val, (mem_supportedSobolevCompletion_iff b b _ isOpen_Ioi u.val).mpr
      (((mem_supportedSobolevCompletion_iff b b _ isOpen_Ioo u.val).mp u.property).mono
        fun _ h hx => h fun h' => hx h'.1)⟩
  intro u v huv
  have he : i u = i v := lowerCutoffMellinLinear_injective b N c hc (funext fun z => congrFun huv z.val)
  exact Subtype.ext (congrArg (fun w : Cutoff b N (Ioi c) => w.val) he)

/-- The entire realization determines the normalized Paley–Wiener space. -/
def compactLineRealization (b : ℝ) (N : ℕ) (c : ℝ) :
    Line b N (Ioo c 0) →ₗ[ℂ] (ℂ → ℂ) :=
  (compactCutoffMellinLinear b N c).comp (supportedMellinLineEquiv b N (Ioo c 0)).symm.toLinearMap

/-- The realization of the middle and right terms of the exact sequence. -/
def lowerLineRealization (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    Line b N (Ioi c) →ₗ[ℂ] (LeftPlane b → ℂ) :=
  (lowerCutoffMellinLinear b N c hc).comp (supportedMellinLineEquiv b N (Ioi c)).symm.toLinearMap

theorem compactLineRealization_onMellin (b : ℝ) (N : ℕ) (c : ℝ) (u : Cutoff b N (Ioo c 0)) :
    compactLineRealization b N c (supportedMellinLineEquiv b N (Ioo c 0) u) =
      cutoffMellinIntegral u.val 0 := by
  change compactCutoffMellinLinear b N c ((supportedMellinLineEquiv b N (Ioo c 0)).symm
    (supportedMellinLineEquiv b N (Ioo c 0) u)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem lowerLineRealization_onMellin (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0)
    (u : Cutoff b N (Ioi c)) :
    lowerLineRealization b N c hc (supportedMellinLineEquiv b N (Ioi c) u) =
      fun z => cutoffMellinIntegral u.val 0 z.val := by
  change lowerCutoffMellinLinear b N c hc ((supportedMellinLineEquiv b N (Ioi c)).symm
    (supportedMellinLineEquiv b N (Ioi c) u)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem rightPaleyWiener_iff_mem_compactLineRealization (b : ℝ) (N : ℕ) (c : ℝ) (F : ℂ → ℂ) :
    RightPaleyWiener b c N F ↔ F ∈ range (compactLineRealization b N c) := by
  rw [rightPaleyWiener_iff_exists_compactCutoff]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨supportedMellinLineEquiv b N (Ioo c 0) u, compactLineRealization_onMellin b N c u⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(supportedMellinLineEquiv b N (Ioo c 0)).symm v, rfl⟩

theorem leftHardySobolev_iff_mem_positiveLineRealization (b : ℝ) (N : ℕ) (F : ℂ → ℂ) :
    (DifferentiableOn ℂ F (LeftPlane b) ∧ UniformMellinLineBound (Iio b) N F) ↔
      (fun z : LeftPlane b => F z.val) ∈ range (lowerLineRealization b N 0 le_rfl) := by
  constructor
  · rintro ⟨hF, hB⟩
    obtain ⟨u, hu⟩ := exists_cutoffMellinIntegral_of_leftHardySobolev hF hB
    refine ⟨supportedMellinLineEquiv b N (Ioi 0) u, ?_⟩
    rw [lowerLineRealization_onMellin]
    exact funext fun z => (hu z.val z.property).symm
  · rintro ⟨v, hv⟩
    let u := (supportedMellinLineEquiv b N (Ioi 0)).symm v
    let G := cutoffMellinIntegral u.val 0
    have hEq : EqOn F G (LeftPlane b) := fun z hz => (congrFun hv ⟨z, hz⟩).symm
    have hs : 0 ≤ 2 * (N : ℝ) := by positivity
    refine ⟨(cutoffMellinIntegral_differentiableOn le_rfl hs u).congr hEq, ?_⟩
    intro k hk
    refine ⟨2 * Real.pi * ‖u‖ ^ 2, fun r hr => ?_⟩
    have hr' : r < b := hr
    have hi (y : ℝ) : iteratedDeriv k F (⟨r, y⟩ : ℂ) =
        cutoffMellinIntegral u.val k (⟨r, y⟩ : ℂ) := by
      have hn : F =ᶠ[𝓝 (⟨r, y⟩ : ℂ)] G :=
        (show ∀ᶠ z in 𝓝 (⟨r, y⟩ : ℂ), z ∈ LeftPlane b from
          (isOpen_Iio.preimage Complex.continuous_re).mem_nhds (show (⟨r, y⟩ : ℂ) ∈ LeftPlane b from hr)).mono hEq
      rw [hn.iteratedDeriv_eq, iteratedDeriv_cutoffMellinIntegral le_rfl hs u k hr']
    simpa only [hi, mul_zero, Real.exp_zero, mul_one] using
      cutoffMellinIntegral_line_bound le_rfl le_rfl hr' hk u

/-- The normalized Hardy norm is the binomially weighted sum of the squared
derivative seminorms, with the Mellin Plancherel factor. -/
def hardyMellinNormSq (D : Set ℝ) (N : ℕ) (F : ℂ → ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) *
    sSup {E : ℝ | ∃ r ∈ D, E = ∫ y : ℝ, ‖iteratedDeriv (k : ℕ) F (⟨r, y⟩ : ℂ)‖ ^ 2}

theorem positiveCutoff_hardyMellinNormSq (b : ℝ) (N : ℕ) (u : Cutoff b N (Ioi 0)) :
    hardyMellinNormSq (Iio b) N (cutoffMellinIntegral u.val 0) = ‖u‖ ^ 2 := by
  unfold hardyMellinNormSq
  have E (k : Fin (N + 1)) :
      sSup {E : ℝ | ∃ r ∈ Iio b,
        E = ∫ y : ℝ, ‖iteratedDeriv (k : ℕ) (cutoffMellinIntegral u.val 0) (⟨r, y⟩ : ℂ)‖ ^ 2} =
      (2 * Real.pi) * ‖cutoffMellinTraceL2 le_rfl (Nat.lt_succ_iff.mp k.isLt) u
        ⟨b, mem_Iic.mpr le_rfl⟩‖ ^ 2 :=
    (positiveCutoff_mellin_energy_isLUB (Nat.lt_succ_iff.mp k.isLt) u).csSup_eq
      ⟨_, b - 1, by simp, rfl⟩
  simp_rw [E]
  have hP : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [Finset.mul_sum]
  have hterm (q x : ℝ) : (2 * Real.pi)⁻¹ * (q * ((2 * Real.pi) * x)) = q * x := by
    field_simp
  simp_rw [hterm]
  exact cutoffMellinTraceL2_endpoint_norm_sum u

private theorem hardyMellinNormSq_right_reflect (b : ℝ) (N : ℕ) (F : ℂ → ℂ) :
    hardyMellinNormSq (Ioi b) N F =
      hardyMellinNormSq (Iio (-b)) N (fun z => F (-z)) := by
  unfold hardyMellinNormSq
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have he (r : ℝ) :
      (∫ y : ℝ, ‖iteratedDeriv (k : ℕ) (fun z => F (-z)) (⟨-r, y⟩ : ℂ)‖ ^ 2) =
        ∫ y : ℝ, ‖iteratedDeriv (k : ℕ) F (⟨r, y⟩ : ℂ)‖ ^ 2 := by
    have hp (y : ℝ) :
        iteratedDeriv (k : ℕ) (fun z => F (-z)) (⟨-r, y⟩ : ℂ) =
          (-1 : ℂ) ^ (k : ℕ) • iteratedDeriv (k : ℕ) F (⟨r, -y⟩ : ℂ) := by
      rw [iteratedDeriv_comp_neg]
      have hh : -(⟨-r, y⟩ : ℂ) = (⟨r, -y⟩ : ℂ) := Complex.ext (neg_neg _) rfl
      rw [hh]
    simp_rw [hp, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact integral_neg_eq_self (fun y : ℝ => ‖iteratedDeriv (k : ℕ) F (⟨r, y⟩ : ℂ)‖ ^ 2) volume
  congr 2
  ext x
  constructor
  · rintro ⟨r, hr, hx⟩
    exact ⟨-r, mem_Iio.mpr (neg_lt_neg (show b < r from hr)), hx.trans (he r).symm⟩
  · rintro ⟨r, hr, hx⟩
    exact ⟨-r, mem_Ioi.mpr (by simpa only [neg_neg] using neg_lt_neg (show r < -b from hr)),
      hx.trans (by simpa only [neg_neg] using he (-r))⟩

theorem compactCutoff_hardyMellinNormSq (b c : ℝ) (N : ℕ) (u : Cutoff b N (Ioo c 0)) :
    hardyMellinNormSq (Ioi b) N (cutoffMellinIntegral u.val 0) = ‖u‖ ^ 2 := by
  obtain ⟨v, hv, hnorm⟩ := exists_reflectedCompactClass u
  have he := reflectedMellinIntegral_eq hv
  have hr : (fun z : ℂ => cutoffMellinIntegral u.val 0 (-z)) = cutoffMellinIntegral v.val 0 := by
    funext z
    exact (congrFun he (-z)).trans (by rw [neg_neg])
  rw [hardyMellinNormSq_right_reflect, hr, positiveCutoff_hardyMellinNormSq, hnorm]

/-- The corrected scalar Paley–Wiener theorem, 9.2.1.2. The line spaces
are Hilbert models of the actual analytic targets. The analytic realization
of the left inclusion is restriction, and the quotient is the Mellin
transform of the positive-logarithm cutoff. -/
theorem hardySobolev_paleyWiener_exact_sequence (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    let L := Cutoff b N (Ioo c 0)
    let M := Cutoff b N (Ioi c)
    let R := Cutoff b N (Ioi 0)
    let L' := Line b N (Ioo c 0)
    let M' := Line b N (Ioi c)
    let R' := Line b N (Ioi 0)
    let A := compactLineRealization b N c
    let B := lowerLineRealization b N c hc
    let C := lowerLineRealization b N 0 le_rfl
    (∃ P : StripSobolev b b (2 * (N : ℝ)) →L[ℂ] StripSobolev b b (2 * (N : ℝ)),
      IsStarProjection P ∧ P.IsPositive ∧
      range P = (supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi c) : Set _) ∧
      ∀ u, (P u : ℝ → ℂ) =ᵐ[volume] (Ici c).indicator (u : ℝ → ℂ)) ∧
    ((supportedMellinLineCompletion b N (Ioi c) : Set (MellinTraceHilbert N)) =
      closure {T | ∃ f : PositiveRealExponentialDecay univ, HasCompactSupport f.val ∧
        tsupport f.val ⊆ Ioi c ∧ mellinLineTest b N f = T}) ∧
    (Injective A ∧ Injective B ∧ Injective C) ∧
    (∀ F : ℂ → ℂ, RightPaleyWiener b c N F ↔ F ∈ range A) ∧
    (∀ F : ℂ → ℂ, (DifferentiableOn ℂ F (LeftPlane b) ∧ UniformMellinLineBound (Iio b) N F) ↔
      (fun z : LeftPlane b => F z.val) ∈ range C) ∧
    (∀ v : L', hardyMellinNormSq (Ioi b) N (A v) = ‖v‖ ^ 2) ∧
    (∀ (v : R') (F : ℂ → ℂ), (∀ z : LeftPlane b, F z.val = C v z) →
      hardyMellinNormSq (Iio b) N F = ‖v‖ ^ 2) ∧
    ∃ (i : L →L[ℂ] M) (p : M →L[ℂ] R) (i' : L' →L[ℂ] M') (p' : M' →L[ℂ] R'),
      (∀ f : L, (i f).val = f.val) ∧
      (∀ f : M, ((p f).val : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (f.val : ℝ → ℂ)) ∧
      (∀ f, supportedMellinLineEquiv b N (Ioi c) (i f) =
        i' (supportedMellinLineEquiv b N (Ioo c 0) f)) ∧
      (∀ f, supportedMellinLineEquiv b N (Ioi 0) (p f) =
        p' (supportedMellinLineEquiv b N (Ioi c) f)) ∧
      (∀ (v : L') (z : LeftPlane b), B (i' v) z = A v z.val) ∧
      (Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p) ∧
      (Injective i' ∧ IsClosed (range i') ∧ Exact i' p' ∧ Surjective p' ∧ IsOpenMap p') := by
  intro L M R L' M' R' A B C
  let hL := supportedMellinLineEquiv b N (Ioo c 0)
  let hM := supportedMellinLineEquiv b N (Ioi c)
  let hR := supportedMellinLineEquiv b N (Ioi 0)
  refine ⟨supportedSobolev_lowerCutoff_eq_projection b b (2 * (N : ℝ)) c,
    supportedMellinLineCompletion_eq_closure_of_compactTests b N isOpen_Ioi,
    ⟨(compactCutoffMellinLinear_injective b N c hc).comp hL.symm.toLinearEquiv.injective,
    (lowerCutoffMellinLinear_injective b N c hc).comp hM.symm.toLinearEquiv.injective,
    (lowerCutoffMellinLinear_injective b N 0 le_rfl).comp hR.symm.toLinearEquiv.injective⟩,
    rightPaleyWiener_iff_mem_compactLineRealization b N c,
    leftHardySobolev_iff_mem_positiveLineRealization b N, ?_, ?_, ?_⟩
  · intro v
    let u := hL.symm v
    change hardyMellinNormSq (Ioi b) N (cutoffMellinIntegral u.val 0) = _
    exact (compactCutoff_hardyMellinNormSq b c N u).trans (congrArg (· ^ 2) (hL.symm.norm_map v))
  · intro v F hF
    let u := hR.symm v
    have hEq (k : ℕ) (r : ℝ) (hr : r < b) (y : ℝ) :
        iteratedDeriv k F (⟨r, y⟩ : ℂ) =
          iteratedDeriv k (cutoffMellinIntegral u.val 0) (⟨r, y⟩ : ℂ) := by
      have hmem : (⟨r, y⟩ : ℂ) ∈ LeftPlane b := hr
      have ho : IsOpen (LeftPlane b) := isOpen_Iio.preimage Complex.continuous_re
      have he : F =ᶠ[𝓝 (⟨r, y⟩ : ℂ)] cutoffMellinIntegral u.val 0 :=
        (show ∀ᶠ z in 𝓝 (⟨r, y⟩ : ℂ), z ∈ LeftPlane b from ho.mem_nhds hmem).mono
          fun z hz => hF ⟨z, hz⟩
      exact he.iteratedDeriv_eq k
    have hnorm : hardyMellinNormSq (Iio b) N F =
        hardyMellinNormSq (Iio b) N (cutoffMellinIntegral u.val 0) := by
      unfold hardyMellinNormSq
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      ext E
      exact exists_congr fun r => and_congr_right fun (hr : r < b) => by simp [hEq k r hr]
    rw [hnorm, positiveCutoff_hardyMellinNormSq, hR.symm.norm_map]
  · obtain ⟨i, p, i', p', hi, hp, hib, hpb, hsrc, htar⟩ := supportedMellinLine_cutoff_diagram b N c hc
    refine ⟨i, p, i', p', hi, hp, hib, hpb, ?_, hsrc, htar⟩
    intro v z
    obtain ⟨u, rfl⟩ := hL.surjective v
    change lowerLineRealization b N c hc (i' (supportedMellinLineEquiv b N (Ioo c 0) u)) z =
      compactLineRealization b N c (supportedMellinLineEquiv b N (Ioo c 0) u) z.val
    rw [← hib, lowerLineRealization_onMellin, compactLineRealization_onMellin]
    change cutoffMellinIntegral (i u).val 0 z.val = cutoffMellinIntegral u.val 0 z.val
    rw [hi]

end
end Masullo
