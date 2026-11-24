import ElementarySchwartzTranslation
import ElementarySchwartzCutoffs
import Mathlib.Analysis.Calculus.MeanValue

open Filter Function Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "A" => ElementaryLCAModel m n r F
local notation "S" => ElementarySchwartz m n r F
local notation "P" => MvPolynomial (Fin m ⊕ Fin r) ℂ

private def translationMonomial (α : Fin m → ℕ) (δ : Fin r → ℕ) (x : X) (a : Fin r → ℤ) : ℂ :=
  (∏ j, (x.1 j : ℂ) ^ α j) * ∏ j, (a j : ℂ) ^ δ j

set_option maxHeartbeats 750000 in
private theorem exists_nearby_weighted_derivative_seminorm (α : Fin m → ℕ) (δ : Fin r → ℕ) (k : ℕ) :
    ∃ q : Seminorm ℂ S, Continuous q ∧
      ∀ (f : S) (x y : X) (a : Fin r → ℤ) (b : F), dist y x ≤ 1 →
        ‖translationMonomial α δ x a‖ *
          ‖iteratedFDeriv ℝ k (fun z => f (elementaryCover z a b)) y‖ ≤ q f := by
  let p : P := (∏ j, (2 + MvPolynomial.X (Sum.inl j) ^ 2) ^ α j) *
    ∏ j, (2 + MvPolynomial.X (Sum.inr j) ^ 2) ^ δ j
  obtain ⟨q, hq, hest⟩ := exists_elementary_weighted_iterated_seminorm (n := n) (F := F) p k
  refine ⟨q, hq, fun f x y a b hxy => ?_⟩
  apply le_trans _ (hest f y a b)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he : MvPolynomial.eval (elementaryGrowthVariables (elementaryCover y a b)) p =
      (((∏ j, (2 + (y.1 j) ^ 2) ^ α j) * ∏ j, (2 + (a j : ℝ) ^ 2) ^ δ j : ℝ) : ℂ) := by
    simp only [p, map_mul, map_prod, map_pow, map_add, map_ofNat, MvPolynomial.eval_X,
      elementaryGrowthVariables, Sum.elim_inl, Sum.elim_inr, elementaryCover,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_ofNat, Complex.ofReal_intCast]
  rw [he, Complex.norm_real, Real.norm_of_nonneg (by positivity), translationMonomial, norm_mul,
    norm_prod, norm_prod]
  apply mul_le_mul
  · apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
    intro j _
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have hd : |x.1 j - y.1 j| ≤ 1 := by
      have h := (PiLp.norm_apply_le (x - y).1 j).trans (norm_fst_le (x - y))
      rw [← dist_eq_norm, dist_comm] at h
      exact h.trans hxy
    have hx : |x.1 j| ≤ |y.1 j| + 1 := by
      calc
        |x.1 j| = |y.1 j + (x.1 j - y.1 j)| := by congr 1; ring
        _ ≤ |y.1 j| + |x.1 j - y.1 j| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl hd
    exact hx.trans (by nlinarith [sq_abs (y.1 j), sq_nonneg (|y.1 j| - 1 / 2)])
  · apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
    intro j _
    rw [norm_pow, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    nlinarith [sq_abs (a j : ℝ), sq_nonneg (|(a j : ℝ)| - 1 / 2)]
  · positivity
  · positivity

private theorem translate_cover_partial (h x : X) (a : Fin r → ℤ) (b : F)
    (f : S) (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    elementaryPartial (elementarySchwartz_translate (elementaryCoverHom h) f).val β γ x a b =
      elementaryPartial f β γ (x + h) a b := by
  have he : (fun z : X => (elementarySchwartz_translate (elementaryCoverHom h) f).val (elementaryCover z a b)) =
      fun z => f (elementaryCover (z + h) a b) := by
    funext z
    change f (elementaryCover z a b + elementaryCoverHom h) = _
    rw [elementaryCover_add]
  rw [elementaryPartial_eq_basis, elementaryPartial_eq_basis, he]
  exact congrArg (fun D => D (fun j => elementaryFibreBasis m n ((elementaryDirectionList β γ).get j)))
    (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun z : X => f (elementaryCover z a b))
      (elementaryDirectionList β γ).length h x)

set_option maxHeartbeats 1000000 in
/-- Uniform control of translations by short lifts, and a first-order bound
on the difference from the identity. -/
private theorem exists_translation_seminorm_bounds (i : ElementarySchwartzIndex m n r) :
    ∃ p q : Seminorm ℂ S, Continuous p ∧ Continuous q ∧ ∀ (h : X) (f : S), ‖h‖ ≤ 1 →
      elementarySchwartzSeminorm i (elementarySchwartz_translate (elementaryCoverHom h) f) ≤ p f ∧
      elementarySchwartzSeminorm i (elementarySchwartz_translate (elementaryCoverHom h) f - f) ≤ q f * ‖h‖ := by
  rcases i with ⟨α, β, γ, δ⟩
  let k := (elementaryDirectionList β γ).length
  obtain ⟨p, hp, hpb⟩ := exists_nearby_weighted_derivative_seminorm (n := n) (F := F) α δ k
  obtain ⟨q, hq, hqb⟩ := exists_nearby_weighted_derivative_seminorm (n := n) (F := F) α δ (k + 1)
  refine ⟨p, q, hp, hq, fun h f hh => ?_⟩
  let t : S →L[ℂ] S := elementarySchwartz_translate (elementaryCoverHom h)
  have hB (u : S) (C : ℝ) (hC : 0 ≤ C)
      (hu : ∀ (x : X) (a : Fin r → ℤ) (b : F),
        ‖translationMonomial α δ x a * elementaryPartial u.val β γ x a b‖ ≤ C) :
      elementarySchwartzSeminorm (α, β, γ, δ) u ≤ C := by
    change (elementarySchwartzBound u.val (α, β, γ, δ)).toReal ≤ C
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (iSup_le fun x => iSup_le fun a => iSup_le fun b => ?_)).trans_eq (ENNReal.toReal_ofReal hC)
    change ‖translationMonomial α δ x a * elementaryPartial u.val β γ x a b‖ₑ ≤ _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hu x a b)
  have hdist (x : X) : dist (x + h) x ≤ 1 := by
    simpa [dist_eq_norm, add_sub_cancel_left] using hh
  let B := fun j : Fin k => elementaryFibreBasis m n ((elementaryDirectionList β γ).get j)
  have hBnorm : ‖B‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j =>
    (elementaryBasis_norm _).le
  constructor
  · apply hB _ _ (apply_nonneg p f)
    intro x a b
    rw [translate_cover_partial, norm_mul, elementaryPartial_eq_basis]
    exact (mul_le_mul_of_nonneg_left
      (ContinuousMultilinearMap.unit_le_opNorm _ hBnorm) (norm_nonneg _)).trans
      (hpb f x (x + h) a b (hdist x))
  · apply hB _ _ (mul_nonneg (apply_nonneg q f) (norm_nonneg h))
    intro x a b
    let W := translationMonomial α δ x a
    let v (z : X) := f (elementaryCover z a b)
    let D := iteratedFDeriv ℝ k v
    have hD (y : X) : DifferentiableAt ℝ D y :=
      ((f.property.1 a b).differentiable_iteratedFDeriv (m := k)
        (by exact_mod_cast WithTop.coe_lt_top k)).differentiableAt
    have he : elementaryPartial (t f - f).val β γ x a b = (D (x + h) - D x) B := by
      rw [elementaryPartial_eq_basis]
      let v₁ (z : X) := (t f).val (elementaryCover z a b)
      change iteratedFDeriv ℝ k (v₁ - v) x B = _
      have h₁ : ContDiff ℝ ∞ v₁ := (t f).property.1 a b
      have h₂ : ContDiff ℝ ∞ v := f.property.1 a b
      have hn : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
      rw [iteratedFDeriv_sub_apply (h₁.of_le hn).contDiffAt (h₂.of_le hn).contDiffAt]
      have hh₁ : v₁ = fun z => v (z + h) := by
        funext z
        exact congrArg (fun y : A => f y) (elementaryCover_add z h a b).symm
      rw [hh₁, iteratedFDeriv_comp_add_right]
    rw [he, norm_mul]
    change ‖W‖ * ‖(D (x + h) - D x) B‖ ≤ _
    by_cases hW : ‖W‖ = 0
    · rw [hW, zero_mul]
      exact mul_nonneg (apply_nonneg q f) (norm_nonneg h)
    have hW₀ : 0 < ‖W‖ := lt_of_le_of_ne (norm_nonneg _) fun he => hW he.symm
    have hder (y : X) (hy : y ∈ Metric.closedBall x 1) : ‖fderiv ℝ D y‖ ≤ q f / ‖W‖ := by
      apply (le_div_iff₀ hW₀).mpr
      rw [mul_comm, norm_fderiv_iteratedFDeriv]
      exact hqb f x y a b hy
    have hm := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hD y) hder (Metric.mem_closedBall_self zero_le_one)
      (show x + h ∈ Metric.closedBall x 1 from hdist x)
    apply (mul_le_mul_of_nonneg_left
      ((ContinuousMultilinearMap.unit_le_opNorm _ hBnorm).trans hm) (norm_nonneg _)).trans
    rw [add_sub_cancel_left, ← mul_assoc, mul_div_cancel₀ _ hW]

private theorem translate_translate (s t : A) (f : S) :
    elementarySchwartz_translate s (elementarySchwartz_translate t f) =
      elementarySchwartz_translate (s + t) f := by
  apply Subtype.ext
  funext x
  simp only [elementarySchwartz_translate_apply, add_assoc]

set_option maxHeartbeats 900000 in
private theorem continuous_lifted_translate :
    Continuous (fun z : X × S => elementarySchwartz_translate (elementaryCoverHom z.1) z.2) := by
  let T (z : X × S) := elementarySchwartz_translate (elementaryCoverHom z.1) z.2
  have h0 (f : S) : T (0, f) = f := by
    apply Subtype.ext
    funext x
    change f (x + elementaryCoverHom (0 : X)) = f x
    rw [map_zero, add_zero]
  have hnear (f : S) : ContinuousAt T (0, f) := by
    change Tendsto T (𝓝 (0, f)) (𝓝 (T (0, f)))
    rw [h0]
    apply (elementarySchwartz_withSeminorms.tendsto_nhds T f).mpr
    intro i ε hε
    obtain ⟨p, q, hp, hq, hb⟩ := exists_translation_seminorm_bounds (F := F) i
    let e (z : X × S) := p (z.2 - f) + q f * ‖z.1‖
    have he : Continuous e := (hp.comp (continuous_snd.sub continuous_const)).add
      (continuous_const.mul continuous_fst.norm)
    have hlim : Tendsto e (𝓝 (0, f)) (𝓝 0) := he.tendsto' _ _ (by simp [e])
    have hsmall : ∀ᶠ z : X × S in 𝓝 (0, f), ‖z.1‖ < 1 :=
      continuous_fst.norm.continuousAt (Iio_mem_nhds (by simp))
    filter_upwards [hsmall, hlim (Iio_mem_nhds hε)] with z hz hεz
    have hsplit : T z - f =
        elementarySchwartz_translate (elementaryCoverHom z.1) (z.2 - f) + (T (z.1, f) - f) := by
      change elementarySchwartz_translate (elementaryCoverHom z.1) z.2 - f = _
      rw [map_sub]
      change _ = _ + (elementarySchwartz_translate (elementaryCoverHom z.1) f - f)
      abel
    rw [hsplit]
    exact ((map_add_le_add (elementarySchwartzSeminorm i) _ _).trans
      (add_le_add (hb z.1 (z.2 - f) hz.le).1 (hb z.1 f hz.le).2)).trans_lt hεz
  apply continuous_iff_continuousAt.mpr
  rintro ⟨u, f⟩
  have hshift : Tendsto (fun z : X × S => (z.1 - u, z.2)) (𝓝 (u, f)) (𝓝 (0, f)) := by
    have hc : Continuous (fun z : X × S => (z.1 - u, z.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    exact hc.tendsto' _ _ (by simp)
  have ht := ((elementarySchwartz_translate (elementaryCoverHom u)).continuous.tendsto _).comp
    ((hnear f).tendsto.comp hshift)
  have hEq (z : X × S) : elementarySchwartz_translate (elementaryCoverHom u) (T (z.1 - u, z.2)) = T z := by
    change elementarySchwartz_translate (elementaryCoverHom u)
      (elementarySchwartz_translate (elementaryCoverHom (z.1 - u)) z.2) = _
    rw [translate_translate, ← map_add, add_sub_cancel]
  have hl : (fun z : X × S => elementarySchwartz_translate (elementaryCoverHom u)
      (T (z.1 - u, z.2))) = T := funext hEq
  change Tendsto (fun z : X × S => elementarySchwartz_translate (elementaryCoverHom u)
    (T (z.1 - u, z.2))) (𝓝 (u, f)) (𝓝 (elementarySchwartz_translate (elementaryCoverHom u) (T (0,f)))) at ht
  rw [hl, h0] at ht
  exact ht

set_option maxHeartbeats 950000 in
/-- Translation is jointly continuous in the shift and the profile in
the mixed Schwartz topology of an elementary group. -/
theorem continuous_elementarySchwartz_translate :
    Continuous (fun z : A × S => elementarySchwartz_translate z.1 z.2) := by
  let D := (Fin r → ℤ) × F
  let Q (z : (X × D) × S) := (elementaryCover z.1.1 z.1.2.1 z.1.2.2, z.2)
  have hQ : IsOpenQuotientMap Q :=
    elementaryCover_openQuotientMap.prodMap (show IsOpenQuotientMap (id : S → S) from .id)
  apply hQ.continuous_comp_iff.mp
  let F₀ (z : (X × S) × D) := elementarySchwartz_translate (elementaryCover z.1.1 z.2.1 z.2.2) z.1.2
  have hF : Continuous F₀ := by
    apply continuous_prod_of_discrete_right.mpr
    intro d
    apply ((elementarySchwartz_translate (elementaryCover (0 : X) d.1 d.2)).continuous.comp
      (continuous_lifted_translate (m := m) (n := n) (r := r) (F := F))).congr
    intro z
    change elementarySchwartz_translate (elementaryCover (0 : X) d.1 d.2)
      (elementarySchwartz_translate (elementaryCoverHom z.1) z.2) =
      elementarySchwartz_translate (elementaryCover z.1 d.1 d.2) z.2
    rw [translate_translate, ← elementaryCover_add, zero_add]
  exact hF.comp (continuous_fst.fst.prodMk continuous_snd |>.prodMk continuous_fst.snd)

end

end Masullo
