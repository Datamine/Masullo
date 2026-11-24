import ElementarySchwartzSymbols
import ExponentialSchwartzCutoffs
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Filter Function Set Topology
open scoped ContDiff ENNReal NNReal SchwartzMap

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "S" => ElementarySchwartz m n r F
local notation "J" => Fin m ⊕ Fin n
local notation "P" => MvPolynomial (Fin m ⊕ Fin r) ℂ

private theorem elementaryBasis_repr_norm_le (x : X) (i : J) :
    ‖(elementaryFibreBasis m n).repr x i‖ ≤ ‖x‖ := by
  cases i with
  | inl i =>
    rw [Module.Basis.prod_repr_inl]
    exact (PiLp.norm_apply_le x.1 i).trans (norm_fst_le x)
  | inr i =>
    rw [Module.Basis.prod_repr_inr]
    exact (PiLp.norm_apply_le x.2 i).trans (norm_snd_le x)

theorem elementaryBasis_norm (i : J) : ‖elementaryFibreBasis m n i‖ = 1 := by
  cases i <;> simp [elementaryFibreBasis, Module.Basis.prod_apply, Prod.norm_def,
    EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis, PiLp.norm_single]

private theorem norm_multilinear_le_sum_elementaryBasis {k : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin k => X) ℂ) :
    ‖D‖ ≤ ∑ t : Fin k → J, ‖D (fun i => elementaryFibreBasis m n (t i))‖ := by
  let B := elementaryFibreBasis m n
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : D v = ∑ t : Fin k → J, (∏ i, B.repr (v i) (t i)) • D (fun i => B (t i)) := by
    change D.toMultilinearMap v = _
    conv_lhs => rw [show v = (fun i => ∑ j, B.repr (v i) j • B j) from
      funext fun i => (B.sum_repr (v i)).symm]
    rw [D.toMultilinearMap.map_sum]
    simp_rw [D.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe]
  rw [he, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [norm_smul, norm_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun i _ => elementaryBasis_repr_norm_le (v i) (t i))) (norm_nonneg _)

/-- A continuous seminorm controls a polynomially weighted norm of the
full derivative on every covering fibre. -/
theorem exists_elementary_weighted_iterated_seminorm (p : P) (k : ℕ) :
    ∃ q : Seminorm ℂ S, Continuous q ∧ ∀ (f : S) (x : X) (a : Fin r → ℤ) (b : F),
      ‖MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) p‖ *
        ‖iteratedFDeriv ℝ k (fun z => f (elementaryCover z a b)) x‖ ≤ q f := by
  classical
  choose β γ hβγ using fun t : Fin k → J => elementaryIteratedFDeriv_basis (r := r) (F := F) t
  let q : Seminorm ℂ S := ∑ t : Fin k → J, ∑ d ∈ p.support, ‖p.coeff d‖₊ • elementarySchwartzSeminorm
    (fun i => d (Sum.inl i), β t, γ t, fun i => d (Sum.inr i))
  refine ⟨q, ?_, fun f x a b => ?_⟩
  · exact Seminorm.continuous_finsetSum fun t _ => Seminorm.continuous_finsetSum fun d _ =>
      (elementarySchwartz_withSeminorms.continuous_seminorm _).const_smul ‖p.coeff d‖₊
  simp only [q, FunLike.coe_sum, Finset.sum_apply]
  apply (mul_le_mul_of_nonneg_left (norm_multilinear_le_sum_elementaryBasis _) (norm_nonneg _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [hβγ t f a b (f.property.1 a b) x]
  let H (d : (Fin m ⊕ Fin r) →₀ ℕ) : Seminorm ℂ S :=
    ‖p.coeff d‖₊ • elementarySchwartzSeminorm
      (fun i => d (Sum.inl i), β t, γ t, fun i => d (Sum.inr i))
  change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ d ∈ p.support, H d) f
  rw [map_sum, Finset.sum_apply]
  exact elementarySchwartz_polynomial_weight_le_monomial_sum p f (β t) (γ t) x a b

private theorem exists_elementary_weighted_iterated_bound (p : P) (f : S) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : X) (a : Fin r → ℤ) (b : F),
      ‖MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) p‖ *
        ‖iteratedFDeriv ℝ k (fun z => f (elementaryCover z a b)) x‖ ≤ C := by
  obtain ⟨q, _, hq⟩ := exists_elementary_weighted_iterated_seminorm (n := n) (F := F) p k
  exact ⟨q f, apply_nonneg q f, hq f⟩

private theorem elementaryLog_polynomial (l : A →+ ℝ) (hl : Continuous l) :
    ∃ q : P, ∀ g : A, MvPolynomial.eval (elementaryGrowthVariables g) q = (l g : ℂ) := by
  obtain ⟨a, b, hab⟩ := elementary_real_addHom_coordinates l hl
  refine ⟨(∑ i, MvPolynomial.C (a i : ℂ) * MvPolynomial.X (Sum.inl i)) +
    ∑ j, MvPolynomial.C (b j : ℂ) * MvPolynomial.X (Sum.inr j), fun g => ?_⟩
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    elementaryGrowthVariables, Sum.elim_inl, Sum.elim_inr, hab g, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]

/-- The logarithmic weight controls every derivative on the covering fibres. -/
theorem exists_elementary_log_derivative_seminorm (l : A →+ ℝ) (hl : Continuous l)
    (N k : ℕ) :
    ∃ q : Seminorm ℂ S, Continuous q ∧ ∀ (f : S) (x : X) (a : Fin r → ℤ) (b : F),
      (1 + |l (elementaryCover x a b)|) ^ N *
        ‖iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x‖ ≤ q f := by
  obtain ⟨p, hp⟩ := elementaryLog_polynomial l hl
  obtain ⟨qPlus, hqPlus, hPlus⟩ :=
    exists_elementary_weighted_iterated_seminorm (n := n) (F := F) ((1 + p) ^ N) k
  obtain ⟨qMinus, hqMinus, hMinus⟩ :=
    exists_elementary_weighted_iterated_seminorm (n := n) (F := F) ((1 - p) ^ N) k
  refine ⟨qPlus + qMinus, hqPlus.add hqMinus, fun f x a b ↦ ?_⟩
  let g := elementaryCover x a b
  let D := ‖iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x‖
  change (1 + |l g|) ^ N * D ≤ qPlus f + qMinus f
  by_cases h : 0 ≤ l g
  · have hb := hPlus f x a b
    change ‖MvPolynomial.eval (elementaryGrowthVariables g) ((1 + p) ^ N)‖ * D ≤ qPlus f at hb
    rw [map_pow, map_add, map_one, hp, norm_pow, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + l g)] at hb
    rw [abs_of_nonneg h]
    exact hb.trans (le_add_of_nonneg_right (apply_nonneg qMinus f))
  · have hb := hMinus f x a b
    change ‖MvPolynomial.eval (elementaryGrowthVariables g) ((1 - p) ^ N)‖ * D ≤ qMinus f at hb
    rw [map_pow, map_sub, map_one, hp, norm_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - l g)] at hb
    rw [abs_of_nonpos (le_of_not_ge h), ← sub_eq_add_neg]
    exact hb.trans (le_add_of_nonneg_left (apply_nonneg qPlus f))

/-- Every power of the absolute value of a real character is controlled by
a continuous Schwartz seminorm, uniformly over the elementary quotient. -/
theorem exists_elementary_log_decay_seminorm (l : A →+ ℝ) (hl : Continuous l) (N : ℕ) :
    ∃ q : Seminorm ℂ S, Continuous q ∧ ∀ (f : S) (g : A),
      (1 + |l g|) ^ N * ‖f g‖ ≤ q f := by
  obtain ⟨q, hq, hb⟩ := exists_elementary_log_derivative_seminorm l hl N 0
  refine ⟨q, hq, fun f g ↦ ?_⟩
  obtain ⟨t, ht⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  have h := hb f (g.1, t) g.2.2.1 g.2.2.2
  simpa only [norm_iteratedFDeriv_zero, ht] using h

private theorem norm_iteratedFDeriv_comp_affine {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℝ → Y) (hf : ContDiff ℝ ∞ f)
    (L : X →L[ℝ] ℝ) (c : ℝ) (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (fun z => f (L z + c)) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x + c)‖ * ‖L‖ ^ k := by
  let g (t : ℝ) := f (t + c)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ k (g ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hg x (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g (L x)) (fun _ => L)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, g, iteratedFDeriv_comp_add_right] using h

private theorem exists_elementaryCover_real_affine (l : A →+ ℝ) (hl : Continuous l) :
    ∃ L : X →L[ℝ] ℝ, ∀ (z : X) (a : Fin r → ℤ) (b : F),
      l (elementaryCover z a b) = L z + l (elementaryCover (0 : X) a b) := by
  let H := l.comp (elementaryCoverHom : X →+ A)
  have hH : Continuous H := hl.comp elementaryCoverHom_continuous
  let L₀ := H.toRealLinearMap hH
  let L : X →L[ℝ] ℝ := ⟨L₀, L₀.continuous_of_finiteDimensional⟩
  refine ⟨L, fun z a b => ?_⟩
  have he := elementaryCover_add (0 : X) z a b
  rw [zero_add] at he
  rw [he, map_add, add_comm]
  rfl

/-- A smooth real multiplier with bounded derivatives, pulled back by a
continuous logarithmic homomorphism, preserves elementary Schwartz functions. -/
theorem elementarySchwartz_mul_boundedLogMultiplier (l : A →+ ℝ) (hl : Continuous l)
    (e : ℝ → ℝ) (he : ContDiff ℝ ∞ e)
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv j e x‖ ≤ C) (f : S) :
    (fun y => e (l y) • f y) ∈ elementarySchwartzSubmodule m n r F := by
  obtain ⟨L,hL⟩ := exists_elementaryCover_real_affine l hl
  let u (a : Fin r → ℤ) (b : F) (z : X) := e (L z + l (elementaryCover (0 : X) a b))
  let v (a : Fin r → ℤ) (b : F) (z : X) := f (elementaryCover z a b)
  have hu (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (u a b) :=
    he.comp (L.contDiff.add contDiff_const)
  let g (y : A) := e (l y) • f y
  have hEq (a : Fin r → ℤ) (b : F) : (fun z : X => g (elementaryCover z a b)) =
      fun z => u a b z • v a b z := funext fun z =>
    congrArg (fun t => e t • v a b z) (hL z a b)
  refine ⟨fun a b => by rw [hEq]; exact (hu a b).smul (f.property.1 a b),?_⟩
  rintro ⟨α,β,γ,δ⟩
  let k := (elementaryDirectionList β γ).length
  let p : P := (∏ j, MvPolynomial.X (Sum.inl j) ^ α j) *
    ∏ j, MvPolynomial.X (Sum.inr j) ^ δ j
  choose B hB hB' using fun j => exists_elementary_weighted_iterated_bound p f j
  choose U hU hU' using hb
  let C := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (U j * ‖L‖ ^ j) * B (k-j)
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun x => iSup_le fun a => iSup_le fun b => ?_
  let W : ℂ := (∏ j, (x.1 j : ℂ) ^ α j) * ∏ j, (a j : ℂ) ^ δ j
  change ‖W * elementaryPartial g β γ x a b‖ₑ ≤ _
  rw [← ofReal_norm, norm_mul]
  apply ENNReal.ofReal_le_ofReal
  have hpart : ‖elementaryPartial g β γ x a b‖ ≤
      ‖iteratedFDeriv ℝ k (fun z => u a b z • v a b z) x‖ := by
    rw [elementaryPartial_eq_basis, hEq]
    apply ContinuousMultilinearMap.unit_le_opNorm
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => (elementaryBasis_norm _).le
  have hD := norm_iteratedFDeriv_smul_le (hu a b) (f.property.1 a b) x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  apply (mul_le_mul_of_nonneg_left (hpart.trans hD) (norm_nonneg _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hw : MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) p = W := by
    simp [p,W,elementaryGrowthVariables,elementaryCover]
  have hV : ‖W‖ * ‖iteratedFDeriv ℝ (k-j) (v a b) x‖ ≤ B (k-j) := by
    rw [← hw]
    exact hB' _ x a b
  have hUj : ‖iteratedFDeriv ℝ j (u a b) x‖ ≤ U j * ‖L‖ ^ j := by
    refine (norm_iteratedFDeriv_comp_affine e he L _ j x).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hU' _ _
  calc
    _ = (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (u a b) x‖ *
        (‖W‖ * ‖iteratedFDeriv ℝ (k-j) (v a b) x‖) := by ring
    _ ≤ _ := by
      have hU₀ := hU j
      gcongr

private def elementaryCutoffError (l : A →+ ℝ) (f : S) (N : ℕ) (g : A) : ℂ :=
  (truncationMultiplier N (l g) - 1) * f g

private theorem elementaryCutoffError_smooth (l : A →+ ℝ) (hl : Continuous l) (f : S) (N : ℕ)
    (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (fun z => elementaryCutoffError l f N (elementaryCover z a b)) := by
  obtain ⟨L, hL⟩ := exists_elementaryCover_real_affine l hl
  have hEq : (fun z : X => elementaryCutoffError l f N (elementaryCover z a b)) =
      fun z => (truncationMultiplier N (L z + l (elementaryCover (0 : X) a b)) - 1) *
        f (elementaryCover z a b) := funext fun z =>
    congrArg (fun t => (truncationMultiplier N t - 1) * f (elementaryCover z a b)) (hL z a b)
  rw [hEq]
  exact ((((truncationMultiplier_growth N).1.comp (L.contDiff.add contDiff_const)).sub contDiff_const)).mul
    (f.property.1 a b)

set_option maxHeartbeats 800000 in
private theorem elementaryCutoffError_bound (l : A →+ ℝ) (hl : Continuous l) (f : S)
    (i : ElementarySchwartzIndex m n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N, elementarySchwartzBound (elementaryCutoffError l f N) i ≤
      ENNReal.ofReal (C / ((N : ℝ) + 1)) := by
  classical
  obtain ⟨L, hL⟩ := exists_elementaryCover_real_affine l hl
  rcases i with ⟨α, β, γ, δ⟩
  let k := (elementaryDirectionList β γ).length
  let p₀ : P := (∏ j, MvPolynomial.X (Sum.inl j) ^ α j) *
    ∏ j, MvPolynomial.X (Sum.inr j) ^ δ j
  obtain ⟨q, hq⟩ := elementaryLog_polynomial l hl
  let p := p₀ * (1 + q ^ 2)
  choose B hB hb using fun j => exists_elementary_weighted_iterated_bound p f j
  choose U hU hUbd using truncationError_scaled_bound
  let C := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (U j * ‖L‖ ^ j) * B (k - j)
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hU j) (by positivity))) (hB _)
  refine ⟨C, hC, fun N => ?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  let W : ℂ := (∏ j, (x.1 j : ℂ) ^ α j) * ∏ j, (a j : ℂ) ^ δ j
  let y := elementaryCover x a b
  change ‖W * elementaryPartial (elementaryCutoffError l f N) β γ x a b‖ₑ ≤ _
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  let e (t : ℝ) := truncationMultiplier N t - 1
  let u (z : X) := e (l (elementaryCover z a b))
  let v (z : X) := f (elementaryCover z a b)
  have hv : ContDiff ℝ ∞ v := f.property.1 a b
  have he : ContDiff ℝ ∞ e := (truncationMultiplier_growth N).1.sub contDiff_const
  have hu : ContDiff ℝ ∞ u := by
    have hEq : u = fun z => e (L z + l (elementaryCover (0 : X) a b)) :=
      funext fun z => congrArg e (hL z a b)
    rw [hEq]
    exact he.comp (L.contDiff.add contDiff_const)
  have hpart : ‖elementaryPartial (elementaryCutoffError l f N) β γ x a b‖ ≤
      ‖iteratedFDeriv ℝ k (fun z => u z * v z) x‖ := by
    rw [elementaryPartial_eq_basis]
    apply ContinuousMultilinearMap.unit_le_opNorm
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => (elementaryBasis_norm _).le)
  have hN₀ : 0 < (N : ℝ) + 1 := by positivity
  by_cases hx : |l y| < (N : ℝ) + 1
  · have hCont : Continuous (fun z : X => |l (elementaryCover z a b)|) := by
      have hEq : (fun z : X => |l (elementaryCover z a b)|) =
          fun z => |L z + l (elementaryCover (0 : X) a b)| :=
        funext fun z => congrArg abs (hL z a b)
      rw [hEq]
      exact (L.continuous.add continuous_const).abs
    have hzero : (fun z => u z * v z) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hCont.continuousAt (Iio_mem_nhds hx)] with z hz
      change (truncationMultiplier N (l (elementaryCover z a b)) - 1) * v z = 0
      rw [truncationMultiplier_one N hz, sub_self, zero_mul]
    rw [(hzero.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] at hpart
    have h0 := norm_eq_zero.mp (le_antisymm hpart (norm_nonneg _))
    rw [h0, mul_zero, norm_zero]
    exact div_nonneg hC hN₀.le
  have hWeight : ‖W‖ * ((N : ℝ) + 1) ≤ ‖MvPolynomial.eval (elementaryGrowthVariables y) p‖ := by
    have h0 : MvPolynomial.eval (elementaryGrowthVariables y) p₀ = W := by
      simp [p₀, W, y, elementaryGrowthVariables, elementaryCover]
    have hp : MvPolynomial.eval (elementaryGrowthVariables y) p = W * ((1 + (l y) ^ 2 : ℝ) : ℂ) := by
      simp [p, h0, hq y]
    have hnorm : ‖MvPolynomial.eval (elementaryGrowthVariables y) p‖ = ‖W‖ * (1 + (l y) ^ 2) := by
      rw [hp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left
      ((le_of_not_gt hx).trans (by nlinarith [sq_abs (l y), sq_nonneg (|l y| - 1 / 2)]))
      (norm_nonneg _)
  have hDer := norm_iteratedFDeriv_mul_le hu hv x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  rw [norm_mul, le_div_iff₀ hN₀, mul_right_comm]
  apply (mul_le_mul hWeight (hpart.trans hDer) (norm_nonneg _) (norm_nonneg _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := norm_iteratedFDeriv_comp_affine e he L (l (elementaryCover (0 : X) a b)) j x
  have hju : ‖iteratedFDeriv ℝ j u x‖ ≤ U j * ‖L‖ ^ j := by
    have hh : (fun z : X => u z) = fun z => e (L z + l (elementaryCover (0 : X) a b)) := by
      funext z
      exact congrArg e (hL z a b)
    rw [show u = _ from hh]
    exact hj.trans (mul_le_mul_of_nonneg_right (by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hUbd j N _) (by positivity))
  have hfj := hb (k - j) x a b
  change _ ≤ (k.choose j : ℝ) * (U j * ‖L‖ ^ j) * B (k - j)
  calc
    _ = (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j u x‖ *
        (‖MvPolynomial.eval (elementaryGrowthVariables y) p‖ * ‖iteratedFDeriv ℝ (k - j) v x‖) := by ring
    _ ≤ _ := by
      have hUj := hU j
      gcongr

/-- Multiplication by the widening smooth logarithmic cutoffs converges
in all defining Schwartz seminorms on an elementary quotient. -/
theorem exists_elementarySchwartz_logCutoff_sequence (l : A →+ ℝ) (hl : Continuous l) (f : S) :
    ∃ u : ℕ → S, Tendsto u atTop (𝓝 f) ∧
      ∀ N g, u N g = truncationMultiplier N (l g) * f g := by
  have hmem (N : ℕ) : elementaryCutoffError l f N ∈ elementarySchwartzSubmodule m n r F := by
    refine ⟨elementaryCutoffError_smooth l hl f N, fun i => ?_⟩
    obtain ⟨C, _, hC⟩ := elementaryCutoffError_bound l hl f i
    exact (hC N).trans_lt ENNReal.ofReal_lt_top
  let e (N : ℕ) : S := ⟨elementaryCutoffError l f N, hmem N⟩
  have he : Tendsto e atTop (𝓝 0) := by
    rw [elementarySchwartz_withSeminorms.tendsto_nhds]
    intro i ε hε
    obtain ⟨C, hC₀, hC⟩ := elementaryCutoffError_bound l hl f i
    have hlim : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    filter_upwards [hlim (Iio_mem_nhds hε)] with N hN
    rw [sub_zero]
    exact ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC N)).trans_eq
      (ENNReal.toReal_ofReal (by positivity))).trans_lt hN
  refine ⟨fun N => e N + f, by simpa using he.add tendsto_const_nhds, fun N g => ?_⟩
  change (truncationMultiplier N (l g) - 1) * f g + f g = _
  ring

set_option maxHeartbeats 900000 in
/-- On the half-space where the exponential is at most one, the twisted
partial is controlled by the Schwartz seminorms of the original profile. -/
private theorem exists_elementary_exponential_halfspace_seminorm (l : A →+ ℝ) (hl : Continuous l)
    (t : ℝ) (i : ElementarySchwartzIndex m n r) :
    ∃ q : Seminorm ℂ S, Continuous q ∧ ∀ (f : S) (x : X) (a : Fin r → ℤ) (b : F), t * l (elementaryCover x a b) ≤ 0 →
      ‖(∏ j, (x.1 j : ℂ) ^ i.1 j) * (∏ j, (a j : ℂ) ^ i.2.2.2 j) *
        elementaryPartial (fun y => Real.exp (t * l y) • f y) i.2.1 i.2.2.1 x a b‖ ≤ q f := by
  obtain ⟨L, hL⟩ := exists_elementaryCover_real_affine l hl
  rcases i with ⟨α, β, γ, δ⟩
  let k := (elementaryDirectionList β γ).length
  let p : P := (∏ j, MvPolynomial.X (Sum.inl j) ^ α j) *
    ∏ j, MvPolynomial.X (Sum.inr j) ^ δ j
  choose B hB hb using fun j => exists_elementary_weighted_iterated_seminorm (n := n) (F := F) p j
  let c (j : ℕ) : ℝ≥0 := ⟨(k.choose j : ℝ) * (‖t‖ ^ j * ‖L‖ ^ j), by positivity⟩
  let Q : Seminorm ℂ S := ∑ j ∈ Finset.range (k + 1), c j • B (k - j)
  refine ⟨Q, Seminorm.continuous_finsetSum (fun j _ => (hB (k-j)).const_smul (c j)), fun f x a b hx => ?_⟩
  have hQ : Q f = ∑ j ∈ Finset.range (k + 1), (c j : ℝ) * B (k-j) f := by
    simp only [Q, FunLike.coe_sum, Finset.sum_apply, smul_apply, NNReal.smul_def, smul_eq_mul]
  let d := l (elementaryCover (0 : X) a b)
  let u (z : X) := Real.exp (t * l (elementaryCover z a b))
  let v (z : X) := f (elementaryCover z a b)
  let e (s : ℝ) := Real.exp (t * s)
  have he : ContDiff ℝ ∞ e := (contDiff_const.mul contDiff_id).exp
  have hue : u = fun z => e (L z + d) := funext fun z => congrArg e (hL z a b)
  have hu : ContDiff ℝ ∞ u := hue ▸ (he.comp (L.contDiff.add contDiff_const))
  have hv : ContDiff ℝ ∞ v := f.property.1 a b
  let W : ℂ := (∏ j, (x.1 j : ℂ) ^ α j) * ∏ j, (a j : ℂ) ^ δ j
  have hp : MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) p = W := by
    simp [p, W, elementaryGrowthVariables, elementaryCover]
  change ‖W * elementaryPartial (fun y => Real.exp (t * l y) • f y) β γ x a b‖ ≤ Q f
  have hpart : ‖elementaryPartial (fun y => Real.exp (t * l y) • f y) β γ x a b‖ ≤
      ‖iteratedFDeriv ℝ k (fun z => u z • v z) x‖ := by
    rw [elementaryPartial_eq_basis]
    apply ContinuousMultilinearMap.unit_le_opNorm
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => (elementaryBasis_norm _).le
  have hDer := norm_iteratedFDeriv_smul_le hu hv x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left (hpart.trans hDer) (norm_nonneg _)).trans
  rw [Finset.mul_sum, hQ]
  apply Finset.sum_le_sum
  intro j _
  have hju : ‖iteratedFDeriv ℝ j u x‖ ≤ ‖t‖ ^ j * ‖L‖ ^ j := by
    rw [hue]
    refine (norm_iteratedFDeriv_comp_affine e he L d j x).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show e = _ from rfl,
      iteratedDeriv_exp_const_mul, norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_of_le_one_right (by positivity)
    exact Real.exp_le_one_iff.mpr (by rwa [← hL x a b])
  have hfv : ‖W‖ * ‖iteratedFDeriv ℝ (k - j) v x‖ ≤ B (k - j) f := by
    rw [← hp]
    exact hb (k - j) f x a b
  calc
    _ = (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j u x‖ *
        (‖W‖ * ‖iteratedFDeriv ℝ (k - j) v x‖) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hju (Nat.cast_nonneg _)) hfv
      (by positivity) (by change 0 ≤ (k.choose j : ℝ) * (‖t‖ ^ j * ‖L‖ ^ j); positivity)

set_option maxHeartbeats 650000 in
/-- Intermediate real exponential twists are Schwartz on each elementary quotient. -/
theorem elementarySchwartz_exponential_between (l : A →+ ℝ) (hl : Continuous l)
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (u v : S)
    (hv : ∀ y, v y = Real.exp ((b - a) * l y) • u y) :
    (fun y => Real.exp ((c - a) * l y) • u y) ∈ elementarySchwartzSubmodule m n r F := by
  let w (y : A) := Real.exp ((c - a) * l y) • u y
  have hw : w = fun y => Real.exp ((c - b) * l y) • v y := by
    funext y
    change Real.exp ((c - a) * l y) • u y = Real.exp ((c - b) * l y) • v y
    rw [hv, smul_smul, ← Real.exp_add]
    congr 2
    ring
  refine ⟨fun p q => ?_, fun i => ?_⟩
  · obtain ⟨L, hL⟩ := exists_elementaryCover_real_affine l hl
    have hEq : (fun z : X => l (elementaryCover z p q)) =
        fun z => L z + l (elementaryCover (0 : X) p q) := funext fun z => hL z p q
    have hs : ContDiff ℝ ∞ (fun z : X => l (elementaryCover z p q)) :=
      hEq.symm ▸ (L.contDiff.add contDiff_const)
    exact ((contDiff_const.mul hs).exp).smul (u.property.1 p q)
  · obtain ⟨Cu, _, hU⟩ := exists_elementary_exponential_halfspace_seminorm l hl (c - a) i
    obtain ⟨Cv, _, hV⟩ := exists_elementary_exponential_halfspace_seminorm l hl (c - b) i
    apply lt_of_le_of_lt (b := ENNReal.ofReal (Cu u + Cv v)) _ ENNReal.ofReal_lt_top
    refine iSup_le fun x => iSup_le fun p => iSup_le fun q => ?_
    let W : ℂ := (∏ j, (x.1 j : ℂ) ^ i.1 j) * ∏ j, (p j : ℂ) ^ i.2.2.2 j
    change ‖W * elementaryPartial w i.2.1 i.2.2.1 x p q‖ₑ ≤ _
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (l (elementaryCover x p q)) 0 with h | h
    · exact (hU u x p q (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hac) h)).trans
        (le_add_of_nonneg_right (apply_nonneg Cv v))
    · rw [hw]
      exact (hV v x p q (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcb) h)).trans
        (le_add_of_nonneg_left (apply_nonneg Cu u))

/-- Each intermediate Schwartz seminorm is controlled by continuous seminorms
of the two endpoint profiles. -/
theorem exists_elementarySchwartz_exponential_between_bound (l : A →+ ℝ) (hl : Continuous l)
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (i : ElementarySchwartzIndex m n r) :
    ∃ q₁ q₂ : Seminorm ℂ S, Continuous q₁ ∧ Continuous q₂ ∧
      ∀ u w v : S,
        (∀ y, w y = Real.exp ((c-a) * l y) • u y) →
        (∀ y, w y = Real.exp ((c-b) * l y) • v y) →
        elementarySchwartzSeminorm i w ≤ q₁ u + q₂ v := by
  obtain ⟨q₁,h₁,h₁'⟩ := exists_elementary_exponential_halfspace_seminorm l hl (c-a) i
  obtain ⟨q₂,h₂,h₂'⟩ := exists_elementary_exponential_halfspace_seminorm l hl (c-b) i
  refine ⟨q₁,q₂,h₁,h₂,fun u w v hu hv => ?_⟩
  have hb : elementarySchwartzBound w.val i ≤ ENNReal.ofReal (q₁ u + q₂ v) := by
    refine iSup_le fun x => iSup_le fun p => iSup_le fun q => ?_
    let W : ℂ := (∏ j, (x.1 j : ℂ) ^ i.1 j) * ∏ j, (p j : ℂ) ^ i.2.2.2 j
    change ‖W * elementaryPartial w.val i.2.1 i.2.2.1 x p q‖ₑ ≤ _
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (l (elementaryCover x p q)) 0 with h | h
    · rw [show w.val = _ from funext hu]
      exact (h₁' u x p q (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hac) h)).trans
        (le_add_of_nonneg_right (apply_nonneg q₂ v))
    · rw [show w.val = _ from funext hv]
      exact (h₂' v x p q (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcb) h)).trans
        (le_add_of_nonneg_left (apply_nonneg q₁ u))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

set_option maxHeartbeats 950000 in
/-- A continuous real additive coordinate is a multiplier of the elementary
Schwartz space. A polynomial weight absorbs its affine growth on each fibre. -/
theorem elementarySchwartz_mul_realHom (l : A →+ ℝ) (hl : Continuous l) (f : S) :
    (fun y => l y • f y) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  obtain ⟨L, hL⟩ := exists_elementaryCover_real_affine l hl
  obtain ⟨q, hq⟩ := elementaryLog_polynomial l hl
  let g (y : A) := l y • f y
  have hAffine (a : Fin r → ℤ) (b : F) :
      (fun z : X => l (elementaryCover z a b)) =
        fun z => L z + l (elementaryCover (0 : X) a b) :=
    funext fun z => hL z a b
  have hSmooth (a : Fin r → ℤ) (b : F) :
      ContDiff ℝ ∞ (fun z : X => l (elementaryCover z a b)) :=
    (hAffine a b).symm ▸ (L.contDiff.add contDiff_const)
  refine ⟨fun a b => (hSmooth a b).smul (f.property.1 a b), fun i => ?_⟩
  rcases i with ⟨α, β, γ, δ⟩
  let k := (elementaryDirectionList β γ).length
  let p₀ : P := (∏ j, MvPolynomial.X (Sum.inl j) ^ α j) *
     ∏ j, MvPolynomial.X (Sum.inr j) ^ δ j
  let p := p₀ * (1 + q ^ 2)
  choose B hB hb using fun j => exists_elementary_weighted_iterated_bound p f j
  let C := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (2 * ‖L‖ ^ j) * B (k - j)
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun x => iSup_le fun a => iSup_le fun b => ?_
  let W : ℂ := (∏ j, (x.1 j : ℂ) ^ α j) * ∏ j, (a j : ℂ) ^ δ j
  let y := elementaryCover x a b
  change ‖W * elementaryPartial g β γ x a b‖ₑ ≤ _
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  let u (z : X) := l (elementaryCover z a b)
  let v (z : X) := f (elementaryCover z a b)
  have hpart : ‖elementaryPartial g β γ x a b‖ ≤
      ‖iteratedFDeriv ℝ k (fun z => u z • v z) x‖ := by
    rw [elementaryPartial_eq_basis]
    apply ContinuousMultilinearMap.unit_le_opNorm
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => (elementaryBasis_norm _).le
  have hDer := norm_iteratedFDeriv_smul_le (hSmooth a b) (f.property.1 a b) x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hEval : ‖MvPolynomial.eval (elementaryGrowthVariables y) p‖ = ‖W‖ * (1 + (l y) ^ 2) := by
    have h0 : MvPolynomial.eval (elementaryGrowthVariables y) p₀ = W := by
      simp [p₀, W, y, elementaryGrowthVariables, elementaryCover]
    have hp : MvPolynomial.eval (elementaryGrowthVariables y) p = W * ((1 + (l y) ^ 2 : ℝ) : ℂ) := by
      simp [p, h0, hq y]
    rw [hp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left (hpart.trans hDer) (norm_nonneg _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hu : ‖iteratedFDeriv ℝ j u x‖ ≤ (2 * ‖L‖ ^ j) * (1 + (l y) ^ 2) := by
    rw [show u = _ from hAffine a b]
    have h := norm_iteratedFDeriv_comp_affine id contDiff_id L
      (l (elementaryCover (0 : X) a b)) j x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← hL x a b] at h
    refine h.trans ?_
    have h' : ‖iteratedDeriv j (id : ℝ → ℝ) (l y)‖ ≤ 2 * (1 + (l y) ^ 2) := by
      rcases j with _ | _ | j
      · simp only [iteratedDeriv_zero, id_eq, Real.norm_eq_abs]
        nlinarith [sq_abs (l y), sq_nonneg (|l y| - 1)]
      · simp [iteratedDeriv_id]
        nlinarith [sq_nonneg (l y)]
      · simp [iteratedDeriv_id]
        positivity
    calc
      _ ≤ (2 * (1 + (l y) ^ 2)) * ‖L‖ ^ j := mul_le_mul_of_nonneg_right h' (by positivity)
      _ = _ := by ring
  calc
    _ = (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j u x‖ *
        (‖W‖ * ‖iteratedFDeriv ℝ (k - j) v x‖) := by ring
    _ ≤ (k.choose j : ℝ) * (2 * ‖L‖ ^ j) *
        (‖MvPolynomial.eval (elementaryGrowthVariables y) p‖ *
          ‖iteratedFDeriv ℝ (k - j) v x‖) := by
      rw [hEval]
      calc
        _ ≤ (k.choose j : ℝ) * ((2 * ‖L‖ ^ j) * (1 + (l y) ^ 2)) *
            (‖W‖ * ‖iteratedFDeriv ℝ (k - j) v x‖) := by gcongr
        _ = _ := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (hb (k - j) x a b)
      positivity

end

end Masullo
