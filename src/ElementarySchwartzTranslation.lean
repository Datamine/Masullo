import ElementarySchwartzSymbols

open Function
open scoped ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "S" => ElementarySchwartz m n r F

/-- Adding covering coordinates adds their images on the elementary quotient. -/
theorem elementaryCover_add_shift
    (x u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a a' : Fin r → ℤ) (b b' : F) :
    elementaryCover x a b + elementaryCover u a' b' =
      elementaryCover (x + u) (a + a') (b + b') := by
  exact Prod.ext rfl (Prod.ext (funext fun j ↦ (AddCircle.coe_add 1 (x.2 j) (u.2 j)).symm) rfl)

private theorem elementarySmooth_translate (s : A) (f : S) (a : Fin r → ℤ) (b : F) :
    ContDiff ℝ ∞ (fun u ↦ f.val (elementaryCover u a b + s)) := by
  obtain ⟨t, ht⟩ := elementaryCover_surjective s.2.2.1 s.2.2.2 s.1 s.2.1
  have hs : (s.1, s.2.1, s.2.2.1, s.2.2.2) = s := rfl
  rw [hs] at ht
  have he : (fun u ↦ f.val (elementaryCover u a b + s)) =
      (fun u ↦ f.val (elementaryCover (u + (s.1, t)) (a + s.2.2.1) (b + s.2.2.2))) := by
    funext u
    apply congrArg f.val
    conv_lhs => rw [← ht]
    exact elementaryCover_add_shift _ _ _ _ _ _
  rw [he]
  exact (f.property.1 (a + s.2.2.1) (b + s.2.2.2)).comp (contDiff_id.add contDiff_const)

private theorem elementaryOrbitWord_translate
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A)) (f : A → ℂ) (s : A) :
    elementaryOrbitWord cs (fun g ↦ f (g + s)) =
      fun g ↦ elementaryOrbitWord cs f (g + s) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [elementaryOrbitWord, ih, elementaryOrbitDeriv]
    funext g
    apply congrArg (fun q : ℝ → ℂ ↦ deriv q 0)
    funext u
    exact congrArg (elementaryOrbitWord cs f) (by abel)

private theorem elementaryGrowthVariables_add (g s : A) (j : Fin m ⊕ Fin r) :
    elementaryGrowthVariables (g + s) j =
      elementaryGrowthVariables g j + elementaryGrowthVariables s j := by
  cases j <;> simp [elementaryGrowthVariables]

private theorem elementarySchwartz_translate_bound (s : A) (i : ElementarySchwartzIndex m n r) :
    ∃ q : Seminorm ℂ S, Continuous q ∧
      ∀ f : S, elementarySchwartzBound (fun g ↦ f.val (g + s)) i ≤ ENNReal.ofReal (q f) := by
  classical
  let p : MvPolynomial (Fin m ⊕ Fin r) ℂ :=
    ∏ j, (MvPolynomial.X j - MvPolynomial.C (elementaryGrowthVariables s j)) ^
      Sum.elim i.1 i.2.2.2 j
  obtain ⟨cs, hcs⟩ := elementaryOrbitWord_partial (r := r) (F := F) i.2.1 i.2.2.1
  obtain ⟨q, hq, hbound⟩ := elementary_polynomialWord_bound cs p
  refine ⟨q, hq, fun f ↦ ?_⟩
  unfold elementarySchwartzBound
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  let g : A := elementaryCover x a b
  have hw : MvPolynomial.eval (elementaryGrowthVariables (g + s)) p =
      (∏ j, (x.1 j : ℂ) ^ i.1 j) * (∏ j, (a j : ℂ) ^ i.2.2.2 j) := by
    dsimp only [p]
    rw [MvPolynomial.eval_prod]
    simp only [MvPolynomial.eval_pow, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C,
      elementaryGrowthVariables_add, add_sub_cancel_right, Fintype.prod_sum_type]
    rfl
  have hd : elementaryOrbitWord cs f (g + s) =
      elementaryPartial (fun g ↦ f.val (g + s)) i.2.1 i.2.2.1 x a b :=
    (congrFun (elementaryOrbitWord_translate cs f s) g).symm.trans
      (hcs _ (elementarySmooth_translate s f) x a b)
  have h := hbound f (g + s)
  rwa [hw, hd] at h

/-- Translation of the argument acts by a continuous linear operator on the
actual mixed-derivative Schwartz space of the elementary group. -/
def elementarySchwartz_translate (s : A) : S →L[ℂ] S := by
  let L : S →ₗ[ℂ] S :=
    { toFun := fun f ↦ ⟨(fun g ↦ f.val (g + s)), elementarySmooth_translate s f, fun i ↦ by
        obtain ⟨q, _, hq⟩ := elementarySchwartz_translate_bound s i
        exact lt_of_le_of_lt (hq f) ENNReal.ofReal_lt_top⟩
      map_add' _ _ := Subtype.ext rfl
      map_smul' _ _ := Subtype.ext rfl }
  refine ⟨L, ?_⟩
  apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
  intro i
  obtain ⟨q, hq, hbound⟩ := elementarySchwartz_translate_bound s i
  apply Seminorm.continuous_of_le hq
  intro f
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound f)).trans_eq
    (ENNReal.toReal_ofReal (apply_nonneg q f))

@[simp] theorem elementarySchwartz_translate_apply (s : A) (f : S) (x : A) :
    (elementarySchwartz_translate s f).val x = f.val (x + s) := rfl

end

end Masullo
