import FiniteGaussTest
import FinitePlaceLaurent
import VectorHolomorphyDerivatives

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo
noncomputable section

set_option maxSynthPendingDepth 8

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev E := ↥(locallyConstantTests (K F v))
private abbrev Phase := (K F v)ˣ →ₜ* Circle

local instance : TopologicalSpace (E F v) := finestLocallyConvexTopology _
local instance : IsTopologicalAddGroup (E F v) := (finest_withSeminorms _).topologicalAddGroup
local instance : ContinuousSMul ℂ (E F v) := (finest_withSeminorms (E F v)).continuousSMul
local instance : PolynormableSpace ℂ (E F v) := (finest_withSeminorms _).toPolynormableSpace

variable [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]
variable (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]

private theorem realPos_eventually : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)

private def finiteRamifiedZetaDistribution (χ : Phase F v) (hχ : ¬finiteZetaUnramified F v χ)
    (z : ℂ) : StrongDual ℂ (E F v) := by
  let A := finiteZetaContinuation F v μ χ
  have ha := finiteZetaContinuation_analytic_of_ramified F v μ χ hχ
  let L : E F v →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ A f z
      map_add' := fun f g ↦ congrFun ((ha (f + g)).eq_of_eventuallyEq ((ha f).add (ha g)) (z₀ := (1 : ℂ)) (by
        filter_upwards [realPos_eventually] with w hw
        change A (f + g) w = A f w + A g w
        simp only [A, ← (finiteZetaContinuation_eq_integral F v μ χ _ w hw).2]
        exact finiteZetaIntegral_add F v μ χ f g w hw)) z
      map_smul' := fun a f ↦ congrFun ((ha (a • f)).eq_of_eventuallyEq
        (analyticOnNhd_const.mul (ha f)) (z₀ := (1 : ℂ)) (by
        filter_upwards [realPos_eventually] with w hw
        change A (a • f) w = a * A f w
        simp only [A, ← (finiteZetaContinuation_eq_integral F v μ χ _ w hw).2]
        exact finiteZetaIntegral_smul F v μ χ a f w)) z }
  exact ⟨L, finest_linear_continuous L⟩

/-- The finite-place reference is the integer-ring indicator in the
unramified case and the inverse character on the unit shell in the ramified case. -/
def finiteWeilNormalizedTest (χ : Phase F v) : E F v :=
  if finiteZetaUnramified F v χ then finiteCompletionIntegerRingTest F v else finiteGaussTest F v χ

/-- The cleared distribution divided by the fixed multiplicative Haar mass
of the integral unit group. -/
def finiteWeilNormalizedDistribution (χ : Phase F v) (z : ℂ) : StrongDual ℂ (E F v) :=
  (μ.real (finitePlaceIntegralUnits F v) : ℂ)⁻¹ •
    if h : finiteZetaUnramified F v χ then finiteZetaClearedDistribution F v μ χ z
    else finiteRamifiedZetaDistribution F v μ χ h z

/-- Each scalar evaluation of the normalized finite-place family is entire. -/
theorem finiteWeilNormalizedDistribution_analytic (χ : Phase F v) (f : E F v) :
    AnalyticOnNhd ℂ (fun z ↦ finiteWeilNormalizedDistribution F v μ χ z f) univ := by
  have h (z : ℂ) : finiteWeilNormalizedDistribution F v μ χ z f =
      (μ.real (finitePlaceIntegralUnits F v) : ℂ)⁻¹ *
        (if finiteZetaUnramified F v χ then finiteZetaClearedDistribution F v μ χ z f
          else finiteZetaContinuation F v μ χ f z) := by
    unfold finiteWeilNormalizedDistribution
    split <;> rfl
  simp_rw [h]
  apply analyticOnNhd_const.mul
  by_cases hχ : finiteZetaUnramified F v χ
  · simpa only [ite_eq_left hχ] using finiteZetaClearedDistribution_analytic F v μ χ f
  · simpa only [ite_eq_right hχ] using finiteZetaContinuation_analytic_of_ramified F v μ χ hχ f

/-- The finite-place family is holomorphic in the full strong dual. -/
theorem finiteWeilNormalizedDistribution_holomorphic (χ : Phase F v) :
    Differentiable ℂ (finiteWeilNormalizedDistribution F v μ χ) := by
  let D := StrongDual ℂ (E F v)
  letI : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI : CompleteSpace D := (locallyConstantTests_strongDual_frechet (K F v)).1
  letI : PolynormableSpace ℂ D := strongDual_withBoundedSeminorms.toPolynormableSpace
  apply differentiableOn_univ.mp
  apply differentiableOn_of_weaklyHolomorphicOn (E := D) isOpen_univ
  intro L
  let b := Module.Free.chooseBasis ℂ (E F v)
  obtain ⟨f, hf⟩ := (finest_strongBidual b).surjective L
  have h (z : ℂ) : L (finiteWeilNormalizedDistribution F v μ χ z) =
      finiteWeilNormalizedDistribution F v μ χ z f := by
    rw [← hf]
    exact finest_strongBidual_apply b f _
  exact (finiteWeilNormalizedDistribution_analytic F v μ χ f).differentiableOn.congr fun z _ ↦ h z

/-- The normalizing reference stays equal to one at the exceptional parameters. -/
theorem finiteWeilNormalizedDistribution_reference (χ : Phase F v) (z : ℂ) :
    finiteWeilNormalizedDistribution F v μ χ z (finiteWeilNormalizedTest F v χ) = 1 := by
  let M : ℂ := μ.real (finitePlaceIntegralUnits F v)
  have hM : M ≠ 0 := by
    dsimp only [M]
    exact_mod_cast (finiteZetaUnitMass_pos F v μ).ne'
  by_cases h : finiteZetaUnramified F v χ
  · simp only [finiteWeilNormalizedTest, finiteWeilNormalizedDistribution, ite_eq_left h, dite_eq_left h,
      smul_apply, smul_eq_mul, finiteZetaClearedDistribution_integerRing_unramified F v μ χ h]
    exact inv_mul_cancel₀ hM
  · have he : finiteZetaContinuation F v μ χ (finiteGaussTest F v χ) = fun _ ↦ M := by
      apply (finiteZetaContinuation_analytic_of_ramified F v μ χ h _).eq_of_eventuallyEq analyticOnNhd_const (z₀ := (1 : ℂ))
      filter_upwards [realPos_eventually] with w hw
      exact (finiteZetaContinuation_eq_integral F v μ χ _ w hw).2.symm.trans
        (finiteGaussTest_mellin F v μ χ w)
    unfold finiteWeilNormalizedTest finiteWeilNormalizedDistribution
    rw [ite_eq_right h, dite_eq_right h]
    change M⁻¹ * finiteZetaContinuation F v μ χ (finiteGaussTest F v χ) z = 1
    rw [he, inv_mul_cancel₀ hM]

private theorem finiteWeilNormalizedDistribution_eq_mul_integral (χ : Phase F v)
    (g : E F v) (w : ℂ) (hw : 0 < w.re) :
    finiteWeilNormalizedDistribution F v μ χ w g =
      (μ.real (finitePlaceIntegralUnits F v) : ℂ)⁻¹ * finiteZetaIntegral F v μ χ g w *
        finiteZetaWeilMultiplier F v χ w := by
  by_cases h : finiteZetaUnramified F v χ
  · simp only [finiteWeilNormalizedDistribution, dite_eq_left h, smul_apply, smul_eq_mul,
      finiteZetaClearedDistribution_eq_mul_integral F v μ χ g w hw, finiteZetaWeilMultiplier,
      ite_eq_left h, mul_assoc, finiteZetaDenominator]
  · unfold finiteWeilNormalizedDistribution finiteZetaWeilMultiplier
    rw [dite_eq_right h, ite_eq_right h, mul_one]
    change (μ.real (finitePlaceIntegralUnits F v) : ℂ)⁻¹ * finiteZetaContinuation F v μ χ g w = _
    rw [← (finiteZetaContinuation_eq_integral F v μ χ g w hw).2]

/-- The normalized distribution is a finite-place eigendistribution at
every spectral parameter, with the same character as the original Tate integral. -/
theorem finiteWeilNormalizedDistribution_translate (χ : Phase F v) (z : ℂ)
    (u : (K F v)ˣ) (f : E F v) :
    finiteWeilNormalizedDistribution F v μ χ z (locallyConstantTestTranslate (K F v) u f) =
      ((χ u : ℂ) * finiteZetaWeight F v z u) * finiteWeilNormalizedDistribution F v μ χ z f := by
  let N := finiteWeilNormalizedDistribution F v μ χ
  have ha (g : E F v) := finiteWeilNormalizedDistribution_analytic F v μ χ g
  have hweight : AnalyticOnNhd ℂ (fun w ↦ (χ u : ℂ) * finiteZetaWeight F v w u) univ := by
    intro w _
    unfold finiteZetaWeight
    fun_prop
  apply congrFun ((ha _).eq_of_eventuallyEq (hweight.mul (ha f)) (z₀ := (1 : ℂ)) ?_) z
  filter_upwards [realPos_eventually] with w hw
  change N w (locallyConstantTestTranslate (K F v) u f) =
    ((χ u : ℂ) * finiteZetaWeight F v w u) * N w f
  rw [finiteWeilNormalizedDistribution_eq_mul_integral F v μ χ _ w hw,
    finiteWeilNormalizedDistribution_eq_mul_integral F v μ χ f w hw, finiteZetaIntegral_translate]
  ring

/-- The local zeta continuation is the normalized distribution times the
Euler factor, including the Haar mass present on the chosen reference. -/
theorem finiteWeilNormalizedDistribution_meromorphic (χ : Phase F v) (f : E F v) (c : ℂ) :
    finiteZetaContinuation F v μ χ f =ᶠ[𝓝[≠] c] fun z ↦
      ((μ.real (finitePlaceIntegralUnits F v) : ℂ) / finiteZetaWeilMultiplier F v χ z) *
        finiteWeilNormalizedDistribution F v μ χ z f := by
  let M : ℂ := μ.real (finitePlaceIntegralUnits F v)
  let D := finiteZetaWeilMultiplier F v χ
  have hM : M ≠ 0 := by
    dsimp only [M]
    exact_mod_cast (finiteZetaUnitMass_pos F v μ).ne'
  let U := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hN : U.Nonempty := ⟨1, by simp [U]⟩
  have hD : AnalyticOnNhd ℂ D univ := finiteZetaWeilMultiplier_analytic F v χ
  have hMer : Meromorphic (fun z ↦ (M / D z) * finiteWeilNormalizedDistribution F v μ χ z f) :=
    fun z ↦ ((Meromorphic.const M z).div (hD z trivial).meromorphicAt).mul
      ((finiteWeilNormalizedDistribution_analytic F v μ χ f) z trivial).meromorphicAt
  apply boundedPoleMellinSpace_unique_germs hU hN
    (meromorphicOn_univ.mp (finiteZetaContinuation_meromorphic F v μ χ f)) hMer _ c
  intro z hz
  have hd : D z ≠ 0 := by
    by_cases hχ : finiteZetaUnramified F v χ
    · simpa only [D, finiteZetaWeilMultiplier, ite_eq_left hχ, finiteZetaDenominator] using
        finiteZetaDenominator_ne_zero_of_pos F v χ z hz
    · simp [D, finiteZetaWeilMultiplier, hχ]
  change _ = M / D z * finiteWeilNormalizedDistribution F v μ χ z f
  rw [← (finiteZetaContinuation_eq_integral F v μ χ f z hz).2,
    finiteWeilNormalizedDistribution_eq_mul_integral F v μ χ f z hz]
  change _ = M / D z * (M⁻¹ * finiteZetaIntegral F v μ χ f z * D z)
  field_simp

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteUnramifiedEigenfunctional_eq_zero (T : E F v →ₗ[ℂ] ℂ)
    (c : (K F v)ˣ → ℂ) (hc : ∀ u : (K F v)ˣ, ‖u.val‖ = 1 → c u = 1)
    (hπ : c (chosenFiniteUniformizer F v) ≠ 0)
    (he : ∀ u f, T (locallyConstantTestTranslate (K F v) u f) = c u * T f)
    (hT : T (finiteCompletionIntegerRingTest F v) = 0) : T = 0 := by
  let π := chosenFiniteUniformizer F v
  let B (n : ℤ) := finitePlaceLaurentBall F v π n
  have hz : ∀ n : ℤ, T (B n).val = 0 := by
    intro n
    have hstep (k : ℤ) : T (B (k + 1)).val = c π * T (B k).val := by
      dsimp only [B]
      rw [← translateRadial_ball F v π k]
      exact he π (B k).val
    induction n using Int.induction_on with
    | zero => rw [show (B 0).val = finiteCompletionIntegerRingTest F v from
        finitePlaceLaurentBall_zero F v π, hT]
    | succ n ih => rw [hstep, ih, mul_zero]
    | pred n ih =>
      apply (mul_eq_zero.mp ?_).resolve_left hπ
      rw [← hstep, sub_add_cancel, ih]
  have hA (f : E F v) : T (principalUnitAverage F v f) = T f := by
    rw [principalUnitAverage_apply]
    have h (u : principalIntegralUnits F v) : T (principalUnitAction F v u f) = T f := by
      change T (locallyConstantTestTranslate _ u.val f) = _
      rw [he, hc u.val u.property, one_mul]
    simp only [h, integral_const, measureReal_def, principalUnitHaar_univ, ENNReal.toReal_one,
      one_smul]
  ext f
  rw [← hA]
  let g : finitePlaceRadial F v := ⟨principalUnitAverage F v f, principalUnitAverage_radial F v f⟩
  letI : TopologicalSpace (LaurentPolynomial ℂ) := finestLocallyConvexTopology _
  let e := finitePlaceLaurentEquiv F v π (chosenFiniteUniformizer_spec F v)
  obtain ⟨P, hP⟩ := e.surjective g
  change T g.val = 0
  rw [← hP]
  clear hP
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Submodule.coe_add, map_add]
    rw [hp, hq, add_zero]
  | C_mul_T k a =>
    rw [← LaurentPolynomial.smul_eq_C_mul, map_smul, Submodule.coe_smul, map_smul]
    rw [finitePlaceLaurentEquiv_monomial F v π (chosenFiniteUniformizer_spec F v), hz k, smul_zero]

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteRamifiedEigenfunctional_eq_zero
    (χ : Phase F v) (hχ : ¬finiteZetaUnramified F v χ) (T : E F v →ₗ[ℂ] ℂ)
    (c : (K F v)ˣ → ℂ) (hc : ∀ u : (K F v)ˣ, ‖u.val‖ = 1 → c u = (χ u : ℂ))
    (he : ∀ u f, T (locallyConstantTestTranslate (K F v) u f) = c u * T f)
    (hT : T (finiteGaussTest F v χ) = 0) : T = 0 := by
  let U := ↥(principalIntegralUnits F v)
  let π := chosenFiniteUniformizer F v
  let q := (v.asIdeal.absNorm : ℝ)
  let ϑ : PontryaginDual U := χ.comp ⟨(principalIntegralUnits F v).subtype, continuous_subtype_val⟩
  have hq : 1 < q := by dsimp only [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have huMem (u : (K F v)ˣ) : u ∈ finitePlaceIntegralUnits F v ↔ ‖u.val‖ = 1 := by
    rw [← finiteZetaShell_zero, finiteZetaShell]
    simp
  have hϑ : ∃ u : U, χ u.val ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (fun u hu ↦ h ⟨u, (huMem u).mp hu⟩)
  let B (n : ℤ) := locallyConstantTestTranslate (K F v) (π ^ n) (finiteGaussTest F v χ)
  have hBzero (n : ℤ) : T (B n) = 0 := by
    change T (locallyConstantTestTranslate _ _ _) = _
    rw [he, hT, mul_zero]
  ext f
  change T f = 0
  have hf : f ∈ ⨆ η : PontryaginDual U, principalUnitIsotype F v η := by
    rw [principalUnitIsotype_span]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (principalUnitIsotype F v) (motive := fun f ↦ T f = 0)
    hf ?_ (map_zero T) ?_
  · intro η g hg
    by_cases hη : η = ϑ
    · subst η
      have hiso (u : U) : principalUnitAction F v u g = (ϑ u : ℂ) • g := hg u
      have h0 : g.val 0 = 0 := by
        obtain ⟨a, ha⟩ := hϑ
        have h := congrArg (fun p : E F v ↦ p.val 0) (hiso a)
        change g.val (a.val⁻¹.val * 0) = (χ a.val : ℂ) * g.val 0 at h
        rw [mul_zero] at h
        have hh := (one_mul _).trans h
        exact (mul_eq_mul_right_iff.mp hh).resolve_left
          (fun h1 ↦ ha (Circle.coe_injective (h1.symm.trans Circle.coe_one.symm)))
      obtain ⟨L, N, -, hbounds⟩ := finiteZetaShell_test_bounds F v g
      have hgSum : g = ∑ n ∈ Finset.Ico L (N : ℤ), g.val (π ^ n).val • B n := by
        apply Subtype.ext
        funext x
        by_cases hx : x = 0
        · subst x
          rw [h0]
          simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
          apply Eq.symm
          apply Finset.sum_eq_zero
          intro n _
          change g.val (π ^ n).val * (finiteGaussTest F v χ).val ((π ^ n)⁻¹.val * 0) = 0
          rw [mul_zero, finiteGaussTest_zero, mul_zero]
        let w := Units.mk0 x hx
        obtain ⟨m, u, hu, hwu⟩ := finiteZetaShell_repr F v w
        let a : U := ⟨u, (huMem u).mp hu⟩
        have hwu' : w = π ^ m * u := hwu.symm
        have hnorm : ‖w.val‖ = q ^ (-m) := by
          rw [hwu', Units.val_mul, norm_mul, finitePlaceUniformizer_norm_zpow, (huMem u).mp hu, mul_one]
        have hsh : w ∈ finiteZetaShell F v m := hnorm
        have hmatch : g.val w.val = (((χ u)⁻¹ : Circle) : ℂ) * g.val (π ^ m).val := by
          have h := congrArg (fun p : E F v ↦ p.val (π ^ m).val) (hiso a⁻¹)
          change g.val ((a⁻¹).val⁻¹.val * (π ^ m).val) =
            ((χ (a⁻¹).val : Circle) : ℂ) * g.val (π ^ m).val at h
          rw [Subgroup.coe_inv, inv_inv, map_inv, mul_comm u.val, ← Units.val_mul, hwu] at h
          exact h
        have hterm (n : ℤ) :
            (B n).val x = if n = m then (((χ u)⁻¹ : Circle) : ℂ) else 0 := by
          let b := (π ^ n)⁻¹ * w
          have hb : b.val = (π ^ n)⁻¹.val * x := rfl
          change (finiteGaussTest F v χ).val b.val = _
          rw [finiteGaussTest_apply_units]
          have hn : ‖b.val‖ = 1 ↔ n = m := by
            change ‖((π ^ n)⁻¹ * w).val‖ = 1 ↔ _
            rw [Units.val_mul, ← zpow_neg, norm_mul,
              finitePlaceUniformizer_norm_zpow, neg_neg, hnorm, ← zpow_add₀ hq₀.ne', ← zpow_zero q]
            rw [(zpow_right_strictMono₀ hq).injective.eq_iff]
            omega
          by_cases h : n = m
          · rw [ite_eq_left (hn.mpr h), ite_eq_left h]
            subst n
            rw [show b = u by dsimp only [b]; rw [hwu', inv_mul_cancel_left]]
          · rw [ite_eq_right (fun h' ↦ h (hn.mp h')), ite_eq_right h]
        simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        simp_rw [hterm]
        by_cases hm : m ∈ Finset.Ico L (N : ℤ)
        · rw [Finset.sum_eq_single_of_mem m hm (fun b _ hb ↦ by rw [ite_eq_right hb, mul_zero]),
            ite_eq_left rfl]
          exact hmatch.trans (mul_comm _ _)
        · have hzero : g.val x = 0 := by
            have h := hbounds m w hsh
            rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hm
            rcases hm with hl | hn
            · exact h.1 hl
            · exact (h.2 hn).trans h0
          rw [hzero]
          exact (Finset.sum_eq_zero (fun b hb ↦ by
            have hne : b ≠ m := fun h ↦ hm (h ▸ hb)
            rw [ite_eq_right hne, mul_zero])).symm
      rw [hgSum, map_sum]
      exact Finset.sum_eq_zero (fun n _ ↦ by rw [map_smul, hBzero, smul_zero])
    · obtain ⟨u, hu⟩ : ∃ u : U, η u ≠ ϑ u := by
        by_contra! h
        exact hη (ContinuousMonoidHom.ext h)
      have hh : principalUnitAction F v u g = (η u : ℂ) • g := hg u
      have h1 := congrArg T hh
      change T (locallyConstantTestTranslate _ u.val g) = T ((η u : ℂ) • g) at h1
      rw [he, hc u.val u.property, map_smul, smul_eq_mul] at h1
      exact (mul_eq_mul_right_iff.mp h1).resolve_left (fun h ↦ hu (Circle.coe_injective h.symm))
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- Every finite-place eigendistribution is the scalar multiple of the
normalized distribution given by its value on the appropriate reference. -/
theorem finiteWeilEigen_distribution_eq (χ : Phase F v) (z : ℂ) (T : StrongDual ℂ (E F v))
    (hT : ∀ u f, T (locallyConstantTestTranslate (K F v) u f) =
      ((χ u : ℂ) * finiteZetaWeight F v z u) * T f) :
    T = T (finiteWeilNormalizedTest F v χ) • finiteWeilNormalizedDistribution F v μ χ z := by
  let N := finiteWeilNormalizedDistribution F v μ χ z
  let f₀ := finiteWeilNormalizedTest F v χ
  let L := T - T f₀ • N
  let c (u : (K F v)ˣ) : ℂ := (χ u : ℂ) * finiteZetaWeight F v z u
  have hN : N f₀ = 1 := finiteWeilNormalizedDistribution_reference F v μ χ z
  have hL : L f₀ = 0 := by
    change T f₀ - T f₀ * N f₀ = 0
    rw [hN, mul_one, sub_self]
  have he (u : (K F v)ˣ) (f : E F v) :
      L.toLinearMap (locallyConstantTestTranslate _ u f) = c u * L.toLinearMap f := by
    change T (locallyConstantTestTranslate _ u f) - T f₀ * N (locallyConstantTestTranslate _ u f) =
      c u * (T f - T f₀ * N f)
    rw [hT, finiteWeilNormalizedDistribution_translate]
    change c u * T f - T f₀ * (c u * N f) = _
    ring
  suffices h : L.toLinearMap = 0 by
    apply sub_eq_zero.mp
    exact ContinuousLinearMap.ext fun f ↦ DFunLike.congr_fun h f
  have hc (u : (K F v)ˣ) (hu : ‖u.val‖ = 1) : c u = (χ u : ℂ) := by
    simp [c, finiteZetaWeight, hu]
  by_cases hχ : finiteZetaUnramified F v χ
  · refine finiteUnramifiedEigenfunctional_eq_zero F v L.toLinearMap c ?_ ?_ he ?_
    · intro u hu
      have hu' : u ∈ finitePlaceIntegralUnits F v := by
        rw [← finiteZetaShell_zero, finiteZetaShell]
        simpa using hu
      rw [hc u hu, hχ u hu', Circle.coe_one]
    · exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)
    · change L (finiteCompletionIntegerRingTest F v) = 0
      simpa only [f₀, finiteWeilNormalizedTest, ite_eq_left hχ] using hL
  · apply finiteRamifiedEigenfunctional_eq_zero F v χ hχ L.toLinearMap c hc he
    change L (finiteGaussTest F v χ) = 0
    simpa only [f₀, finiteWeilNormalizedTest, ite_eq_right hχ] using hL

/-- The eigenspace for the given finite-place quasi-character. -/
def finiteWeilEigenspace (χ : Phase F v) (z : ℂ) : Submodule ℂ (StrongDual ℂ (E F v)) where
  carrier := {T | ∀ u f, T (locallyConstantTestTranslate (K F v) u f) =
    ((χ u : ℂ) * finiteZetaWeight F v z u) * T f}
  zero_mem' := by intro u f; simp
  add_mem' {T S} ht hs := by
    intro u f
    change T (locallyConstantTestTranslate _ u f) + S (locallyConstantTestTranslate _ u f) =
      ((χ u : ℂ) * finiteZetaWeight F v z u) * (T f + S f)
    rw [ht u f, hs u f, mul_add]
  smul_mem' a T ht := by
    intro u f
    change a * T (locallyConstantTestTranslate _ u f) =
      ((χ u : ℂ) * finiteZetaWeight F v z u) * (a * T f)
    rw [ht u f]
    ring

/-- Evaluation on the reference is the coordinate on the one-dimensional
eigenspace, including at the exceptional parameters. -/
def finiteWeilEigenspace_equiv (χ : Phase F v) (z : ℂ) : finiteWeilEigenspace F v χ z ≃ₗ[ℂ] ℂ := by
  let f₀ := finiteWeilNormalizedTest F v χ
  let N : finiteWeilEigenspace F v χ z :=
    ⟨finiteWeilNormalizedDistribution F v μ χ z,
      fun u f ↦ finiteWeilNormalizedDistribution_translate F v μ χ z u f⟩
  refine
    { toFun := fun T ↦ T.val f₀
      invFun := fun a ↦ a • N
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    exact (finiteWeilEigen_distribution_eq F v μ χ z T.val T.property).symm
  · intro a
    change a * finiteWeilNormalizedDistribution F v μ χ z f₀ = a
    rw [finiteWeilNormalizedDistribution_reference F v μ χ z, mul_one]

include μ in
theorem finiteWeilEigenspace_finrank (χ : Phase F v) (z : ℂ) :
    Module.finrank ℂ (finiteWeilEigenspace F v χ z) = 1 :=
  (finiteWeilEigenspace_equiv F v μ χ z).finrank_eq.trans (Module.finrank_self ℂ)

end
end Masullo
