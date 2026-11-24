import ArchimedeanSupportedEigen
import ComplexPointTemperedExpansion

open Filter Function Set Topology
open scoped Classical ComplexConjugate ContDiff SchwartzMap

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℂ, ℂ)

private theorem partial_dilate_apply (v : ℂ) (u : ℂˣ) (f : S) (x : ℂ) :
    complexPartial v (archSchwartzDilation u f) x =
      fderiv ℝ f (u.val⁻¹ * x) (u.val⁻¹ * v) := by
  let L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ u.val⁻¹
  have hf : HasFDerivAt (f : ℂ → ℂ) (fderiv ℝ f (L x)) (L x) :=
    (f.differentiableAt (x := L x)).hasFDerivAt
  have he : (archSchwartzDilation u f : ℂ → ℂ) = (f : ℂ → ℂ) ∘ L := by
    funext y
    rw [archSchwartzDilation_apply]
    change f (y * (u⁻¹ : ℂˣ).val) = f (u.val⁻¹ * y)
    rw [Units.val_inv_eq_inv_val, mul_comm]
  change fderiv ℝ (archSchwartzDilation u f : ℂ → ℂ) x v = _
  rw [he, (hf.comp x L.hasFDerivAt).fderiv]
  rfl

private theorem eval_complex_parts (D : ℂ →L[ℝ] ℂ) (r : ℂ) :
    D r = (r.re : ℂ) * D 1 + (r.im : ℂ) * D Complex.I := by
  have he : r = r.re • (1 : ℂ) + r.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im r).symm
  conv_lhs => rw [he]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

private theorem eval_complex_I_parts (D : ℂ →L[ℝ] ℂ) (r : ℂ) :
    D (r * Complex.I) = -(r.im : ℂ) * D 1 + (r.re : ℂ) * D Complex.I := by
  rw [eval_complex_parts, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_neg]

private theorem wirtingerZ_dilate (u : ℂˣ) (f : S) :
    complexWirtingerZ (archSchwartzDilation u f) =
      u.val⁻¹ • archSchwartzDilation u (complexWirtingerZ f) := by
  ext x
  let r := u.val⁻¹
  let D := fderiv ℝ f (r * x)
  unfold complexWirtingerZ
  simp only [smul_apply, sub_apply, smul_eq_mul, partial_dilate_apply, archSchwartzDilation_apply]
  rw [Units.val_inv_eq_inv_val, mul_comm x u.val⁻¹, mul_one]
  change (1 / 2 : ℂ) * (D r - Complex.I * D (r * Complex.I)) =
    r * ((1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
  rw [eval_complex_parts D r, eval_complex_I_parts]
  conv_rhs => arg 1; rw [← Complex.re_add_im r]
  linear_combination (r.im : ℂ) * D Complex.I / 2 * (Complex.I_mul_I)

private theorem wirtingerBar_dilate (u : ℂˣ) (f : S) :
    complexWirtingerBar (archSchwartzDilation u f) =
      (star u.val⁻¹) • archSchwartzDilation u (complexWirtingerBar f) := by
  ext x
  let r := u.val⁻¹
  let D := fderiv ℝ f (r * x)
  unfold complexWirtingerBar
  simp only [smul_apply, add_apply, smul_eq_mul, partial_dilate_apply, archSchwartzDilation_apply]
  rw [Units.val_inv_eq_inv_val, mul_comm x u.val⁻¹, mul_one]
  change (1 / 2 : ℂ) * (D r + Complex.I * D (r * Complex.I)) =
    star r * ((1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I))
  rw [eval_complex_parts D r, eval_complex_I_parts, Complex.star_def]
  conv_rhs => arg 1; rw [← Complex.re_add_im (conj r), Complex.conj_re, Complex.conj_im, Complex.ofReal_neg]
  linear_combination (r.im : ℂ) * D Complex.I / 2 * (Complex.I_mul_I)

private theorem dilation_power (u : ℂˣ) (A : S →L[ℂ] S) (c : ℂ)
    (hA : ∀ f, A (archSchwartzDilation u f) = c • archSchwartzDilation u (A f))
    (n : ℕ) (f : S) :
    (A ^ n) (archSchwartzDilation u f) = c ^ n • archSchwartzDilation u ((A ^ n) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' A, mul_apply_eq_comp, ih, map_smul, hA, smul_smul, pow_succ]
    rfl

/-- Mixed point jets are diagonal for complex dilation, with the inverse
unit acting on the holomorphic index and its conjugate on the other index. -/
theorem complexSchwartzPointJet_archDilation (a b : ℕ) (u : ℂˣ) (f : S) :
    complexSchwartzPointJet a b (archSchwartzDilation u f) =
      (u.val⁻¹ ^ a * (star u.val⁻¹) ^ b) * complexSchwartzPointJet a b f := by
  unfold complexSchwartzPointJet
  simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
  rw [dilation_power u _ _ (wirtingerBar_dilate u), map_smul,
    dilation_power u _ _ (wirtingerZ_dilate u), smul_smul, map_smul,
    mul_comm ((star u.val⁻¹) ^ b)]
  change _ * archSchwartzDilation u ((complexWirtingerZ ^ a) ((complexWirtingerBar ^ b) f)) 0 = _
  rw [archSchwartzDilation_apply, zero_mul]
  rfl

private theorem exp_slope_injective (a b : ℂ)
    (h : ∀ t : ℝ, Complex.exp ((t : ℂ) * a) = Complex.exp ((t : ℂ) * b)) : a = b := by
  have hd (s : ℂ) : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * s)) s 0 := by
    simpa using ((Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt.mul_const s).cexp
  exact (hd a).unique ((funext h).symm ▸ hd b)

private theorem complex_jet_eigenweight (a b : ℕ) (m : ℤ) (z : ℂ)
    (h : ∀ u : ℂˣ, complexArchUnitWeight m z u = u.val⁻¹ ^ a * (star u.val⁻¹) ^ b) :
    z = -((a + b : ℕ) : ℂ) / 2 ∧ m = (b : ℤ) - a := by
  constructor
  · have he (t : ℝ) : Complex.exp ((t : ℂ) * (2 * z)) =
        Complex.exp ((t : ℂ) * (-((a + b : ℕ) : ℂ))) := by
      let x := Real.exp t
      have hx : 0 < x := Real.exp_pos t
      let u : ℂˣ := Units.mk0 (x : ℂ) (Complex.ofReal_ne_zero.mpr hx.ne')
      have hh := h u
      change ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ m =
        (x : ℂ)⁻¹ ^ a * (star (x : ℂ)⁻¹) ^ b at hh
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
        div_self (Complex.ofReal_ne_zero.mpr hx.ne'), one_zpow, mul_one,
        ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← pow_add,
        ← Complex.ofReal_pow, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hx.ne')),
        ← Complex.ofReal_log (by positivity : 0 ≤ x ^ 2), Real.log_pow] at hh
      change Complex.exp ((↑(2 * Real.log x) : ℂ) * z) = ↑((x⁻¹) ^ (a + b)) at hh
      dsimp only [x] at hh
      rw [Real.log_exp, ← Real.exp_neg, ← Real.exp_nat_mul, Complex.ofReal_exp] at hh
      convert hh using 2 <;> push_cast <;> ring
    have hz := exp_slope_injective _ _ he
    linear_combination hz / 2
  · have he (t : ℝ) : Complex.exp ((t : ℂ) * ((m : ℂ) * Complex.I)) =
        Complex.exp ((t : ℂ) * (((b : ℂ) - a) * Complex.I)) := by
      let w := (t : ℂ) * Complex.I
      let u : ℂˣ := Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)
      have hw : ‖Complex.exp w‖ = 1 := by
        rw [Complex.norm_exp]
        simp [w, Complex.mul_re]
      have hh := h u
      change ((‖Complex.exp w‖ ^ 2 : ℝ) : ℂ) ^ z *
        (Complex.exp w / (‖Complex.exp w‖ : ℂ)) ^ m =
        (Complex.exp w)⁻¹ ^ a * (star (Complex.exp w)⁻¹) ^ b at hh
      have hc : conj (-w) = w := by
        simp only [w, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
      rw [hw, one_pow, Complex.ofReal_one, Complex.one_cpow, one_mul, div_one,
        ← Complex.exp_int_mul, ← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj,
        hc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add] at hh
      convert hh using 2 <;> dsimp only [w] <;> ring
    have hm := mul_right_cancel₀ Complex.I_ne_zero (exp_slope_injective _ _ he)
    exact_mod_cast hm

/-- An origin-supported complex eigendistribution is a single mixed
Wirtinger jet. The radial and angular weights determine its two indices. -/
theorem complexSupportedWeilEigen_eq_jet (T : StrongDual ℂ S)
    (hT : Distribution.dsupport (⇑T) ⊆ {0}) (hT₀ : T ≠ 0) (m : ℤ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f) :
    ∃ (a b : ℕ) (c : ℂ), c ≠ 0 ∧ z = -((a + b : ℕ) : ℂ) / 2 ∧
      m = (b : ℤ) - a ∧ T = c • complexSchwartzPointJet a b := by
  obtain ⟨N, c, hc⟩ := complexPointTemperedDistribution_eq_sum_WirtingerJets T hT
  let W (p : ℕ × ℕ) (u : ℂˣ) := u.val⁻¹ ^ p.1 * (star u.val⁻¹) ^ p.2
  have hweight (p : ℕ × ℕ) (hp : p ∈ complexPointJetIndices N) (hp₀ : c p ≠ 0) :
      z = -((p.1 + p.2 : ℕ) : ℂ) / 2 ∧ m = (p.2 : ℤ) - p.1 := by
    obtain ⟨f, hf⟩ := exists_complexSchwartz_single_pointJet p.1 p.2
    have hf' (q : ℕ × ℕ) : complexSchwartzPointJet q.1 q.2 f = if q = p then 1 else 0 := by
      simpa only [Prod.ext_iff] using hf q.1 q.2
    have hbase : T f = c p := by
      simp_rw [hc f, hf', mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq', ite_eq_left hp]
    apply complex_jet_eigenweight
    intro u
    have hscale : T (archSchwartzDilation u f) = c p * W p u := by
      simp_rw [hc (archSchwartzDilation u f), complexSchwartzPointJet_archDilation, hf',
        mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq', ite_eq_left hp]
    have he := hcov u f
    rw [hscale, hbase, mul_comm (c p)] at he
    exact (mul_right_cancel₀ hp₀ he).symm
  obtain ⟨p, hp, hp₀⟩ : ∃ p ∈ complexPointJetIndices N, c p ≠ 0 := by
    by_contra! h
    apply hT₀
    ext f
    rw [hc]
    exact Finset.sum_eq_zero fun q hq => by rw [h q hq, zero_mul]
  obtain ⟨hz, hm⟩ := hweight p hp hp₀
  refine ⟨p.1, p.2, c p, hp₀, hz, hm, ?_⟩
  ext f
  rw [hc, Finset.sum_eq_single_of_mem p hp]
  · rfl
  · intro q hq hqp
    have hq₀ : c q = 0 := by
      by_contra hn
      obtain ⟨hz', hm'⟩ := hweight q hq hn
      have he : ((p.1 + p.2 : ℕ) : ℂ) = ((q.1 + q.2 : ℕ) : ℂ) := by
        linear_combination 2 * (hz'.symm.trans hz)
      have hn' : p.1 + p.2 = q.1 + q.2 := by exact_mod_cast he
      have hd : (p.2 : ℤ) - p.1 = (q.2 : ℤ) - q.1 := hm.symm.trans hm'
      apply hqp
      exact Prod.ext (by omega) (by omega)
    rw [hq₀, zero_mul]

/-- The origin-supported complex eigendistribution lies on the line of
the normalized family at its parameter. -/
theorem complexSupportedWeilEigen_eq_normalized (T : StrongDual ℂ S)
    (hT : Distribution.dsupport (⇑T) ⊆ {0}) (hT₀ : T ≠ 0) (m : ℤ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f) :
    ∃ c : ℂ, c ≠ 0 ∧ T = c • complexWeilNormalizedFamily m z := by
  obtain ⟨a, b, c, hc, rfl, rfl, hTj⟩ := complexSupportedWeilEigen_eq_jet T hT hT₀ m z hcov
  let f := (complexGammaNormalized_distribution ((b : ℤ) - a)).choose
  have hj := complexWeilNormalizedFamily_eq_jet a b
  change complexSchwartzPointJet a b f ≠ 0 ∧
    complexWeilNormalizedFamily ((b : ℤ) - a) (-((a + b : ℕ) : ℂ) / 2) =
      (complexSchwartzPointJet a b f)⁻¹ • complexSchwartzPointJet a b at hj
  refine ⟨c * complexSchwartzPointJet a b f, mul_ne_zero hc hj.1, ?_⟩
  rw [hTj, hj.2, smul_smul, mul_assoc, mul_inv_cancel₀ hj.1, mul_one]

end
end Masullo
