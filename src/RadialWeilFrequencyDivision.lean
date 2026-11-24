import SmoothFrequencyDivision
import FiniteMomentApproximation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Filter Function MeasureTheory Set Topology
open scoped Classical FourierTransform SchwartzMap

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℝ, ℂ)
abbrev radialFourierSlope (d : ℝ) : ℂ := (↑(-2 * Real.pi * d) : ℂ) * Complex.I

/-- The entire Fourier symbol of a scalar phased real translation difference. -/
def radialWeilDifferenceSymbol (d : ℝ) (a : ℂ) (z : ℂ) : ℂ :=
  1 - a * Complex.exp (radialFourierSlope d * z)

/-- The symbol of a finite list of scalar phased translation differences. -/
def radialWeilProductSymbol (ds : List (ℝ × ℂ)) (z : ℂ) : ℂ :=
  (ds.map fun p ↦ radialWeilDifferenceSymbol p.1 p.2 z).prod

/-- The corresponding product of real translation differences on Schwartz tests. -/
def radialWeilDifferenceProduct (ds : List (ℝ × ℂ)) (f : S) : S :=
  ds.foldr (fun p g ↦ g - p.2 • g.compSubConstCLM ℂ p.1) f

private theorem radialWeilDifferenceSymbol_analytic (d : ℝ) (a z : ℂ) :
    AnalyticAt ℂ (radialWeilDifferenceSymbol d a) z :=
  analyticAt_const.sub (analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp))

private theorem radialWeilDifferenceSymbol_order (d : ℝ) (hd : d ≠ 0) (a z : ℂ) :
    analyticOrderAt (radialWeilDifferenceSymbol d a) z =
      if radialWeilDifferenceSymbol d a z = 0 then 1 else 0 := by
  have ha := radialWeilDifferenceSymbol_analytic d a z
  by_cases hz : radialWeilDifferenceSymbol d a z = 0
  · have hc : radialFourierSlope d ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hd)) Complex.I_ne_zero
    have hd' : HasDerivAt (radialWeilDifferenceSymbol d a)
        (-(a * (Complex.exp (radialFourierSlope d * z) * radialFourierSlope d))) z := by
      apply (((((hasDerivAt_id z).const_mul (radialFourierSlope d)).cexp).const_mul a).const_sub 1).congr_deriv
      simp only [id_eq, mul_one]
    have hr : a * Complex.exp (radialFourierSlope d * z) = 1 := (sub_eq_zero.mp hz).symm
    have hne : deriv (radialWeilDifferenceSymbol d a) z ≠ 0 := by
      rw [hd'.deriv, ← mul_assoc, hr, one_mul, neg_ne_zero]
      exact hc
    exact (ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hne).trans
      (ite_eq_left hz).symm
  · exact (ha.analyticOrderAt_eq_zero.mpr hz).trans (ite_eq_right hz).symm

private theorem radialWeilProductSymbol_analytic (ds : List (ℝ × ℂ)) (z : ℂ) :
    AnalyticAt ℂ (radialWeilProductSymbol ds) z := by
  induction ds with
  | nil => exact analyticAt_const
  | cons p ps ih => exact (radialWeilDifferenceSymbol_analytic p.1 p.2 z).mul ih

/-- Each vanishing factor contributes one to the analytic order. -/
theorem radialWeilProductSymbol_order (ds : List (ℝ × ℂ)) (h : ∀ p ∈ ds, p.1 ≠ 0) (z : ℂ) :
    analyticOrderAt (radialWeilProductSymbol ds) z =
      (ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 z = 0)) : ℕ∞) := by
  induction ds with
  | nil =>
    change analyticOrderAt (fun _ : ℂ ↦ (1 : ℂ)) z = 0
    exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  | cons p ps ih =>
    change analyticOrderAt (radialWeilDifferenceSymbol p.1 p.2 * radialWeilProductSymbol ps) z = _
    rw [analyticOrderAt_mul (radialWeilDifferenceSymbol_analytic p.1 p.2 z)
      (radialWeilProductSymbol_analytic ps z),
      radialWeilDifferenceSymbol_order p.1 (h p (List.mem_cons_self ..)),
      ih (fun q hq ↦ h q (List.mem_cons_of_mem p hq))]
    by_cases hp : radialWeilDifferenceSymbol p.1 p.2 z = 0
    · simp [hp, add_comm]
    · simp [hp]

/-- A compact frequency window carries finitely many jet constraints
for a finite product of nonzero shifts. -/
theorem radialWeilProduct_finite_moment_indices (ds : List (ℝ × ℂ))
    (h : ∀ p ∈ ds, p.1 ≠ 0) (K : Set ℝ) (hK : IsCompact K) :
    {p : ℝ × ℕ | p.1 ∈ K ∧
      p.2 < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 p.1 = 0))}.Finite := by
  have hzeros := finite_analyticZeros_on_compact_real (radialWeilProductSymbol ds)
    (fun ξ ↦ radialWeilProductSymbol_analytic ds ξ)
    (fun ξ ↦ ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 ξ = 0)))
    (fun ξ ↦ radialWeilProductSymbol_order ds h ξ) K hK
  apply (hzeros.prod (Set.finite_lt_nat ds.length)).subset
  rintro ⟨x, n⟩ ⟨hx, hn⟩
  refine ⟨⟨hx, ?_⟩, hn.trans_le List.countP_le_length⟩
  by_contra hnzero
  have hm := radialWeilProductSymbol_order ds h x
  rw [(radialWeilProductSymbol_analytic ds x).analyticOrderAt_eq_zero.mpr hnzero] at hm
  have hcount : ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 x = 0)) = 0 := by
    exact_mod_cast hm.symm
  change n < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 x = 0)) at hn
  exact Nat.not_lt_zero n (hcount ▸ hn)

/-- Real translation in the Schwartz chart multiplies the Fourier transform by a unit phase. -/
theorem radialSchwartz_fourier_compSubConst (f : S) (d ξ : ℝ) :
    𝓕 (f.compSubConstCLM ℂ d) ξ = Complex.exp (radialFourierSlope d * (ξ : ℂ)) * 𝓕 f ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  let v (t : ℝ) := Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) •
    f.compSubConstCLM ℂ d t
  change (∫ t, v t) = _
  rw [← integral_add_right_eq_self v d]
  apply integral_congr_ae
  exact .of_forall fun t ↦ by
    simp only [v, SchwartzMap.compSubConstCLM_apply, add_sub_cancel_right, smul_eq_mul]
    have he : (↑(-2 * Real.pi * (t + d) * ξ) : ℂ) * Complex.I =
        radialFourierSlope d * (ξ : ℂ) + (↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I := by
      dsimp only [radialFourierSlope]
      push_cast
      ring
    change Complex.exp ((↑(-2 * Real.pi * (t + d) * ξ) : ℂ) * Complex.I) * f t =
      Complex.exp (radialFourierSlope d * (ξ : ℂ)) * (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * f t)
    rw [he, Complex.exp_add, mul_assoc]

/-- The finite Schwartz difference product has exactly the stated Fourier symbol. -/
theorem fourier_radialWeilDifferenceProduct (ds : List (ℝ × ℂ)) (f : S) (ξ : ℝ) :
    𝓕 (radialWeilDifferenceProduct ds f) ξ =
      radialWeilProductSymbol ds ξ * 𝓕 f ξ := by
  induction ds with
  | nil => simp [radialWeilDifferenceProduct, radialWeilProductSymbol]
  | cons p ps ih =>
    let g := radialWeilDifferenceProduct ps f
    change 𝓕 (g - p.2 • g.compSubConstCLM ℂ p.1) ξ =
      (radialWeilDifferenceSymbol p.1 p.2 ξ * radialWeilProductSymbol ps ξ) * 𝓕 f ξ
    let A := FourierTransform.fourierCLM ℂ S
    change A (g - p.2 • g.compSubConstCLM ℂ p.1) ξ = _
    rw [map_sub, map_smul]
    change 𝓕 g ξ - p.2 * 𝓕 (g.compSubConstCLM ℂ p.1) ξ = _
    rw [radialSchwartz_fourier_compSubConst]
    change 𝓕 (radialWeilDifferenceProduct ps f) ξ - _ = _
    rw [ih, radialWeilDifferenceSymbol]
    ring

/-- The Schwartz Fourier jets are the logarithmic polynomial moments,
with the exact factor from Mathlib's Fourier convention. -/
theorem radialSchwartz_fourierJet_eq_moment (f : S) (j : ℕ) (ξ : ℝ) :
    iteratedDeriv j ((𝓕 f : S) : ℝ → ℂ) ξ =
      radialFourierSlope 1 ^ j * ∫ t : ℝ, (t : ℂ)^j * f t * Complex.exp (radialFourierSlope t * (ξ : ℂ)) := by
  have heq (t : ℝ) : radialFourierSlope t = radialFourierSlope 1 * (t : ℂ) := by
    dsimp only [radialFourierSlope]
    push_cast
    ring
  let H (n : ℕ) (x t : ℝ) := (radialFourierSlope t)^n * f t * Complex.exp (radialFourierSlope t * (x : ℂ))
  have hnorm (n : ℕ) (x t : ℝ) : ‖H n x t‖ = ‖radialFourierSlope 1‖ ^ n * (‖t‖ ^ n * ‖f t‖) := by
    have hExp : ‖Complex.exp (radialFourierSlope t * (x : ℂ))‖ = 1 := by
      simp [radialFourierSlope, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have ht : ‖radialFourierSlope t‖ = ‖radialFourierSlope 1‖ * ‖t‖ := by
      rw [heq, norm_mul, Complex.norm_real]
    calc
      ‖H n x t‖ = ‖radialFourierSlope t‖ ^ n * ‖f t‖ := by
        change ‖(radialFourierSlope t)^n * f t * Complex.exp (radialFourierSlope t * (x : ℂ))‖ = _
        rw [norm_mul, hExp, mul_one, norm_mul, norm_pow]
      _ = _ := by rw [ht, mul_pow, mul_assoc]
  have hI (n : ℕ) (x : ℝ) : Integrable (H n x) := by
    have hC : Continuous (H n x) := by
      have ha : Continuous radialFourierSlope := by unfold radialFourierSlope; fun_prop
      exact ((ha.pow n).mul f.continuous).mul ((ha.mul continuous_const).cexp)
    apply ((f.integrable_pow_mul volume n).const_mul (‖radialFourierSlope 1‖^n)).mono'
      hC.aestronglyMeasurable
    exact .of_forall fun t ↦ (hnorm n x t).le
  have hdiff (n : ℕ) (x : ℝ) : HasDerivAt (fun y : ℝ ↦ ∫ t, H n y t)
      (∫ t, H (n+1) x t) x := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := H n) (F' := H (n+1))
      (bound := fun t ↦ ‖radialFourierSlope 1‖^(n+1) * (‖t‖^(n+1) * ‖f t‖))
      univ_mem (.of_forall fun y ↦ (hI n y).aestronglyMeasurable) (hI n x)
      (hI (n+1) x).aestronglyMeasurable (.of_forall fun t y _ ↦ (hnorm (n+1) y t).le)
      ((f.integrable_pow_mul volume (n+1)).const_mul _) ?_).2
    refine .of_forall fun t y _ ↦ ?_
    have hcast : HasDerivAt (fun q : ℝ ↦ (q : ℂ)) 1 y :=
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    convert ((hcast.const_mul (radialFourierSlope t)).cexp.const_mul ((radialFourierSlope t)^n * f t)) using 1 <;>
      first | rfl | (simp [H, pow_succ]; ring)
  have h0 : ((𝓕 f : S) : ℝ → ℂ) = fun x ↦ ∫ t, H 0 x t := by
    funext x
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact .of_forall fun t ↦ by
      simp only [H, pow_zero, one_mul, smul_eq_mul, mul_comm (f t)]
      congr 2
      dsimp only [radialFourierSlope]
      push_cast
      ring
  have he (n : ℕ) : iteratedDeriv n ((𝓕 f : S) : ℝ → ℂ) = fun x ↦ ∫ t, H n x t := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using h0
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext fun x ↦ (hdiff n x).deriv
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun t ↦ by
    change (radialFourierSlope t)^j * f t * Complex.exp (radialFourierSlope t * (ξ : ℂ)) =
      radialFourierSlope 1 ^ j * ((t : ℂ)^j * f t * Complex.exp (radialFourierSlope t * (ξ : ℂ)))
    have hp : (radialFourierSlope t)^j = radialFourierSlope 1 ^ j * (t : ℂ)^j := by rw [heq, mul_pow]
    rw [hp]
    ring

/-- A band-limited Schwartz profile whose Fourier jets vanish through
the required multiplicity is an exact image of the radial difference product.
A preimage can be chosen with support in the same frequency window. -/
theorem radialWeilDifferenceProduct_exists_bandlimited_preimage
    (ds : List (ℝ × ℂ)) (h : ∀ p ∈ ds, p.1 ≠ 0) (f : S)
    (hf : HasCompactSupport (𝓕 f : S))
    (hjets : ∀ ξ : ℝ, ∀ j < ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 ξ = 0)),
      iteratedDeriv j ((𝓕 f : S) : ℝ → ℂ) ξ = 0) :
    ∃ g : S, tsupport ((𝓕 g : S) : ℝ → ℂ) ⊆ tsupport ((𝓕 f : S) : ℝ → ℂ) ∧
      radialWeilDifferenceProduct ds g = f := by
  obtain ⟨q, hq, he⟩ := exists_compactSchwartz_divide_analytic
    (radialWeilProductSymbol ds) (fun ξ ↦ radialWeilProductSymbol_analytic ds ξ)
    (fun ξ ↦ ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 ξ = 0)))
    (fun ξ ↦ radialWeilProductSymbol_order ds h ξ) (𝓕 f) hf hjets
  refine ⟨𝓕⁻ q, ?_, ?_⟩
  · rw [FourierTransform.fourier_fourierInv_eq]
    exact hq
  · apply (FourierTransform.fourierCLE ℂ S).injective
    change 𝓕 (radialWeilDifferenceProduct ds (𝓕⁻ q)) = 𝓕 f
    ext ξ
    rw [fourier_radialWeilDifferenceProduct, FourierTransform.fourier_fourierInv_eq]
    exact he ξ

/-- The band-limited division criterion can be stated directly in terms
of the scalar logarithmic moments used by the orbital range. -/
theorem radialWeilDifferenceProduct_exists_of_bandlimited_moments
    (ds : List (ℝ × ℂ)) (h : ∀ p ∈ ds, p.1 ≠ 0) (f : S)
    (hf : HasCompactSupport (𝓕 f : S))
    (hm : ∀ ξ : ℝ, ∀ j < ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 ξ = 0)),
      (∫ t : ℝ, (t : ℂ)^j * f t * Complex.exp (radialFourierSlope t * (ξ : ℂ))) = 0) :
    ∃ g : S, tsupport ((𝓕 g : S) : ℝ → ℂ) ⊆ tsupport ((𝓕 f : S) : ℝ → ℂ) ∧
      radialWeilDifferenceProduct ds g = f := by
  apply radialWeilDifferenceProduct_exists_bandlimited_preimage ds h f hf
  intro ξ j hj
  rw [radialSchwartz_fourierJet_eq_moment, hm ξ j hj, mul_zero]

/-- A compact frequency window permits exact finite jet correction before
division. A vector in the closure of tests in that window belongs to the
closure of the difference range if its continuous jet functionals vanish,
provided the Schwartz realization intertwines the differences. -/
theorem mem_closure_difference_range_of_frequencyWindow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ds : List (ℝ × ℂ)) (h : ∀ p ∈ ds, p.1 ≠ 0) (K : Set ℝ) (hK : IsCompact K)
    (J : S →ₗ[ℂ] E) (P : E →L[ℂ] E)
    (hP : ∀ f, P (J f) = J (radialWeilDifferenceProduct ds f))
    (M : ℝ × ℕ → E →L[ℂ] ℂ)
    (hM : ∀ k : ℝ × ℕ, k.1 ∈ K →
      k.2 < ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 k.1 = 0)) →
      ∀ f, M k (J f) = iteratedDeriv k.2 ((𝓕 f : S) : ℝ → ℂ) k.1)
    (x : E)
    (hx : x ∈ closure (J '' {f : S | tsupport ((𝓕 f : S) : ℝ → ℂ) ⊆ K}))
    (hzer : ∀ k : ℝ × ℕ, k.1 ∈ K →
      k.2 < ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 k.1 = 0)) →
      M k x = 0) :
    x ∈ closure (range P) := by
  let F := FourierTransform.fourierCLM ℂ S
  let B : Submodule ℂ S :=
    { carrier := {f | tsupport (F f : ℝ → ℂ) ⊆ K}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        change tsupport (F (f + g) : ℝ → ℂ) ⊆ K
        rw [map_add]
        apply closure_minimal _ hK.isClosed
        intro ξ hξ
        by_contra hn
        have h0 (p : S) (hp : tsupport (F p : ℝ → ℂ) ⊆ K) : F p ξ = 0 :=
          notMem_support.mp (fun hh ↦ hn (hp (subset_closure hh)))
        exact (mem_support.mp hξ) (by simp [h0 f hf, h0 g hg])
      smul_mem' := by
        intro a f hf
        change tsupport (F (a • f) : ℝ → ℂ) ⊆ K
        rw [map_smul]
        exact (tsupport_smul_subset_right (fun _ : ℝ ↦ a) (F f : ℝ → ℂ)).trans hf }
  let A := B.map J
  let I := {p : ℝ × ℕ | p.1 ∈ K ∧
    p.2 < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 p.1 = 0))}
  letI : Finite I := (radialWeilProduct_finite_moment_indices ds h K hK).to_subtype
  have hxA : x ∈ A.topologicalClosure := hx
  have hc := mem_closure_tests_with_finite_moments A (fun i : I ↦ M i.val) x hxA
    (fun i ↦ hzer i.val i.property.1 i.property.2)
  apply closure_mono _ hc
  rintro y ⟨⟨f, hf, rfl⟩, hy⟩
  have hfK : tsupport ((𝓕 f : S) : ℝ → ℂ) ⊆ K := hf
  have hfc : HasCompactSupport (𝓕 f : S) := hK.of_isClosed_subset isClosed_closure hfK
  have hjets (ξ : ℝ) (j : ℕ)
      (hj : j < ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 ξ = 0))) :
      iteratedDeriv j ((𝓕 f : S) : ℝ → ℂ) ξ = 0 := by
    by_cases hξ : ξ ∈ K
    · exact (hM (ξ,j) hξ hj f).symm.trans (hy ⟨(ξ,j), hξ, hj⟩)
    · have hz := notMem_tsupport_iff_eventuallyEq.mp (fun hp ↦ hξ (hfK hp))
      rw [hz.iteratedDeriv_eq j]
      simp
  obtain ⟨g, _, hg⟩ := radialWeilDifferenceProduct_exists_bandlimited_preimage ds h f hfc hjets
  exact ⟨J g, (hP g).trans (congrArg J hg)⟩

end
end Masullo
