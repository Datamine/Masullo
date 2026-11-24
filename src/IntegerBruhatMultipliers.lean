import BruhatSchwartzStrict
import ElementarySchwartzSymbols

open Function Set Topology
open scoped ContDiff ENNReal NNReal BigOperators

namespace Masullo

noncomputable section

section Elementary

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "P" => MvPolynomial (Fin m ⊕ Fin r) ℂ

omit [DiscreteTopology F] in
set_option maxHeartbeats 1200000 in
private theorem elementary_integerMultiplier_mem
    (l : A →+ ℤ) (hl : Continuous l) (u : ℤ → ℂ) {C : ℝ} {d : ℕ} (hC : 0 ≤ C)
    (hu : ∀ z : ℤ, ‖u z‖ ≤ C * (1 + |(z : ℝ)|) ^ d)
    (f : ElementarySchwartz m n r F) :
    (fun x ↦ u (l x) * f.val x) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let g (x : A) := u (l x) * f.val x
  have hconst (a : Fin r → ℤ) (b : F) (x : E) :
      l (elementaryCover x a b) = l (elementaryCover (0 : E) a b) := by
    let e : E → ℤ := fun y ↦ l (elementaryCover y a b)
    have hcont : Continuous e := hl.comp (by
      show Continuous (fun y : E ↦ elementaryCover y a b)
      exact continuous_fst.prodMk
        ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
          ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const))
    exact (isPreconnected_univ.image e hcont.continuousOn).subsingleton
      (mem_image_of_mem e (mem_univ x)) (mem_image_of_mem e (mem_univ 0))
  have he (a : Fin r → ℤ) (b : F) :
      (fun x : E ↦ g (elementaryCover x a b)) =
        fun x : E ↦ u (l (elementaryCover (0 : E) a b)) • f.val (elementaryCover x a b) :=
    funext fun x ↦ by simp only [g, hconst a b x, smul_eq_mul]
  change (∀ a b, ContDiff ℝ ∞ (fun x : E ↦ g (elementaryCover x a b))) ∧
    ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)
  refine ⟨fun a b ↦ he a b ▸ (f.property.1 a b).const_smul _, fun i ↦ ?_⟩
  let h : A →+ ℝ := (Int.castAddHom ℝ).comp l
  obtain ⟨c, e, hce⟩ := elementary_real_addHom_coordinates h
    ((continuous_of_discreteTopology : Continuous (fun z : ℤ ↦ (z : ℝ))).comp hl)
  let L : P :=
    (∑ j, MvPolynomial.C (c j : ℂ) * MvPolynomial.X (Sum.inl j)) +
      (∑ j, MvPolynomial.C (e j : ℂ) * MvPolynomial.X (Sum.inr j))
  let W : P :=
    (∏ j, MvPolynomial.X (Sum.inl j) ^ i.1 j) *
      (∏ j, MvPolynomial.X (Sum.inr j) ^ i.2.2.2 j)
  let Q : P := W * (1 + L ^ 2) ^ d
  let M : ℝ := ∑ j ∈ Q.support, ‖Q.coeff j‖ * elementarySchwartzSeminorm
    (fun k ↦ j (Sum.inl k), i.2.1, i.2.2.1, fun k ↦ j (Sum.inr k)) f
  apply lt_of_le_of_lt (show elementarySchwartzBound g i ≤ ENNReal.ofReal (C * 2 ^ d * M) from ?_)
    ENNReal.ofReal_lt_top
  unfold elementarySchwartzBound
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  let z := l (elementaryCover x a b)
  let w := (∏ j, (x.1 j : ℂ) ^ i.1 j) * (∏ j, (a j : ℂ) ^ i.2.2.2 j)
  let v := Sum.elim (fun j ↦ (x.1 j : ℂ)) (fun j ↦ (a j : ℂ))
  have hvL : MvPolynomial.eval v L = ((z : ℝ) : ℂ) := by
    have hz := congrArg (fun x : ℝ ↦ (x : ℂ)) (hce (elementaryCover x a b)).symm
    simpa [L, v, elementaryCover, h, z] using hz
  have hvW : MvPolynomial.eval v W = w := by simp [v, W, w]
  have hpart : elementaryPartial g i.2.1 i.2.2.1 x a b =
      u z * elementaryPartial f i.2.1 i.2.2.1 x a b := by
    dsimp only [elementaryPartial]
    rw [he a b, iteratedFDeriv_const_smul_apply' ((f.property.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))]
    change u (l (elementaryCover 0 a b)) * _ = _
    rw [show z = l (elementaryCover 0 a b) from hconst a b x]
    rfl
  have hpow : (1 + |(z : ℝ)|) ^ d ≤ 2 ^ d * (1 + (z : ℝ) ^ 2) ^ d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_abs (z : ℝ), sq_nonneg (|(z : ℝ)| - 1)]
  have hEval : ‖MvPolynomial.eval v Q‖ = ‖w‖ * (1 + (z : ℝ) ^ 2) ^ d := by
    simp only [Q, map_mul, map_pow, map_add, map_one, hvL, hvW, norm_mul]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_pow,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hB : ‖MvPolynomial.eval v Q‖ * ‖elementaryPartial f i.2.1 i.2.2.1 x a b‖ ≤ M :=
    elementarySchwartz_polynomial_weight_le_monomial_sum Q f i.2.1 i.2.2.1 x a b
  have hR : ‖w * elementaryPartial g i.2.1 i.2.2.1 x a b‖ ≤ C * 2 ^ d * M := by
    rw [hEval] at hB
    calc
      _ = ‖w‖ * (‖u z‖ * ‖elementaryPartial f i.2.1 i.2.2.1 x a b‖) :=
        (norm_mul w _).trans (congrArg (‖w‖ * ·)
          ((congrArg norm hpart).trans (norm_mul _ _)))
      _ ≤ ‖w‖ * ((C * (1 + |(z : ℝ)|) ^ d) * ‖elementaryPartial f i.2.1 i.2.2.1 x a b‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hu z) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖w‖ * ((C * (2 ^ d * (1 + (z : ℝ) ^ 2) ^ d)) *
          ‖elementaryPartial f i.2.1 i.2.2.1 x a b‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (norm_nonneg _)) (norm_nonneg _)
      _ = C * 2 ^ d * (‖w‖ * (1 + (z : ℝ) ^ 2) ^ d *
          ‖elementaryPartial f i.2.1 i.2.2.1 x a b‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  exact (ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top (by
    dsimp [M]; positivity)).2 hR

end Elementary

set_option maxHeartbeats 1200000 in
/-- On the integer group, every symbol of at most polynomial growth is a
multiplier of the full Schwartz–Bruhat space. -/
theorem integerBruhat_mem_mul_of_polynomial (u : ℤ → ℂ) {C : ℝ} {d : ℕ} (hC : 0 ≤ C)
    (hu : ∀ z : ℤ, ‖u z‖ ≤ C * (1 + |(z : ℝ)|) ^ d)
    (f : BruhatSchwartz (Multiplicative ℤ)) :
    (fun x : Multiplicative ℤ ↦ u x.toAdd * f.val x) ∈ bruhatSchwartzSubmodule := by
  obtain ⟨p, v, hv⟩ := f.property
  let A := ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
  have hK : IsCompact (p.1.kernel : Set (Multiplicative ℤ)) := by
    rw [← lcaDualAnnihilator_annihilator p.1.kernel p.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ p.1.annihilator_open
  letI : Finite p.1.kernel := hK.finite_of_discrete.to_subtype
  have hk : p.1.kernel ≤ ⊥ := by
    intro x hx
    obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (⟨x, hx⟩ : p.1.kernel))
    have h := congrArg (fun a : p.1.kernel ↦ a.val.toAdd) he
    change n * x.toAdd = (0 : ℤ) at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn.ne')
  have hker : p.1.kernel.comap p.1.upper.val.subtype ≤ p.1.upper.val.subtype.ker :=
    fun x hx ↦ hk hx
  let l₀ : p.1.StageQuotient →* Multiplicative ℤ := QuotientGroup.lift _ p.1.upper.val.subtype hker
  let l : A →+ ℤ := (l₀.comp p.2.equiv.symm.toMulEquiv.toMonoidHom).toAdditive
  have hl₀ : Continuous l₀ :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_subtype_val
  have hl : Continuous l :=
    (continuous_toAdd.comp (hl₀.comp p.2.equiv.symm.continuous)).comp continuous_ofAdd
  let w : p.Space := ⟨_, elementary_integerMultiplier_mem l hl u hC hu v⟩
  refine ⟨p, w, funext fun x ↦ ?_⟩
  rw [← hv]
  by_cases hx : x ∈ p.1.upper.val
  · let y : p.1.upper.val := ⟨x, hx⟩
    change p.1.realizeSchwartz p.2 w y.val = u y.val.toAdd * p.1.realizeSchwartz p.2 v y.val
    rw [p.1.realizeSchwartz_apply_of_mem p.2 w y, p.1.realizeSchwartz_apply_of_mem p.2 v y]
    have he : l (p.1.stageCoordinates p.2 y).toAdd = y.val.toAdd := by
      change (l₀ (p.2.equiv.symm (p.2.equiv (QuotientGroup.mk y)))).toAdd = _
      rw [p.2.equiv.symm_apply_apply]
      rfl
    change u (l (p.1.stageCoordinates p.2 y).toAdd) * _ = _
    rw [he]
  · change p.1.realizeSchwartz p.2 w x = u x.toAdd * p.1.realizeSchwartz p.2 v x
    rw [p.1.realizeSchwartz_apply_of_not_mem p.2 w x hx, p.1.realizeSchwartz_apply_of_not_mem p.2 v x hx,
      mul_zero]

end

end Masullo
