/-
The joint growth and product argument adapts RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at a1d61084d11ef14e3119178113488c654be4da80
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import ElementarySchwartzFiberAverage

open Function
open scoped ContDiff ENNReal NNReal BigOperators

namespace Masullo

noncomputable section

section Derivative

variable {m n r m' n' r' : ℕ} {F F' : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']

local notation "A" => ElementaryLCAModel m n r F
local notation "B" => ElementaryLCAModel m' n' r' F'
local notation "V" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

private theorem fderiv_elementaryPullback (p : A →+ B) (hp : Continuous p)
    (s : ElementarySchwartz m' n' r' F') (v u : V) (a : Fin r → ℤ) (b : F) :
    fderiv ℝ (fun w ↦ s (p (elementaryCover w a b))) u v =
      elementarySchwartz_derivative (elementaryMapDirection p hp (elementaryOneParameter v)) s
        (p (elementaryCover u a b)) := by
  rw [← elementaryOrbitDeriv_cover (elementaryOneParameter v) v (fun _ ↦ rfl)
    (fun z ↦ s (p z)) a b u
    ((elementaryContDiff_hom p hp s s.property.1 a b).differentiable (by simp) u),
    elementarySchwartz_derivative_apply]
  unfold elementaryOrbitDeriv
  congr 1
  funext t
  exact congrArg s.val (map_add p _ _)

omit [DiscreteTopology F] in
private theorem elementary_growthPolynomial (d : A →+ ℝ) (hd : Continuous d) :
    ∃ R : MvPolynomial (Fin m ⊕ Fin r) ℂ, ∀ x : A,
      MvPolynomial.eval (elementaryGrowthVariables x) R = (d x : ℂ) := by
  obtain ⟨l, z, hz⟩ := elementary_real_addHom_coordinates d hd
  refine ⟨(∑ i, MvPolynomial.C (l i : ℂ) * MvPolynomial.X (Sum.inl i)) +
    (∑ i, MvPolynomial.C (z i : ℂ) * MvPolynomial.X (Sum.inr i)), fun x ↦ ?_⟩
  simp [hz, elementaryGrowthVariables, Complex.ofReal_sum, Complex.ofReal_mul]

end Derivative

private abbrev growthEval {l k h : ℕ} {U : Type*}
    (R : MvPolynomial (Fin l ⊕ Fin h) ℂ) (x : ElementaryLCAModel l k h U) :=
  MvPolynomial.eval (elementaryGrowthVariables x) R

section Product

variable {m n r m₁ n₁ r₁ m₂ n₂ r₂ : ℕ} {F F₁ F₂ : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F₁] [TopologicalSpace F₁] [DiscreteTopology F₁] [Finite F₁]
  [AddCommGroup F₂] [TopologicalSpace F₂] [DiscreteTopology F₂] [Finite F₂]

local notation "A" => ElementaryLCAModel m n r F
local notation "B" => ElementaryLCAModel m₁ n₁ r₁ F₁
local notation "C" => ElementaryLCAModel m₂ n₂ r₂ F₂
local notation "S" => ElementarySchwartz m₁ n₁ r₁ F₁
local notation "T" => ElementarySchwartz m₂ n₂ r₂ F₂
local notation "J" => Fin m ⊕ Fin r
local notation "V" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1400000 in
/-- The product of two pullbacks is Schwartz if their growth coordinates
control every noncompact coordinate of the source. -/
theorem elementarySchwartz_graph_mem (p : A →+ B) (q : A →+ C) (hp : Continuous p)
    (hq : Continuous q) (hcoord : ∀ j : J, ∃ (a : B →+ ℝ) (b : C →+ ℝ),
      Continuous a ∧ Continuous b ∧
      ∀ x, elementaryGrowthCoordinate j x = a (p x) + b (q x)) (s : S) (t : T) :
    (fun x ↦ s (p x) * t (q x)) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  choose a b ha hb hab using hcoord
  choose P hP using fun j ↦ elementary_growthPolynomial (a j) (ha j)
  choose Q hQ using fun j ↦ elementary_growthPolynomial (b j) (hb j)
  let w (l : List J) (x : A) := (l.map (fun j ↦ (elementaryGrowthCoordinate j x : ℂ))).prod
  have hw (l : List J) (R : MvPolynomial (Fin m₁ ⊕ Fin r₁) ℂ)
      (U : MvPolynomial (Fin m₂ ⊕ Fin r₂) ℂ) (s : S) (t : T) : ∃ M : ℝ, ∀ x : A,
        ‖w l x * ((growthEval R (p x) * s (p x)) * (growthEval U (q x) * t (q x)))‖ ≤ M := by
    induction l generalizing R U with
    | nil =>
      obtain ⟨c, _, hc⟩ := elementary_polynomialWord_bound [] R (n := n₁) (F := F₁)
      obtain ⟨d, _, hd⟩ := elementary_polynomialWord_bound [] U (n := n₂) (F := F₂)
      refine ⟨c s * d t, fun x ↦ ?_⟩
      change ‖1 * ((_ * s (p x)) * (_ * t (q x)))‖ ≤ _
      rw [one_mul, norm_mul]
      exact mul_le_mul (hc s (p x)) (hd t (q x)) (norm_nonneg _) (apply_nonneg _ _)
    | cons j l ih =>
      obtain ⟨c, hc⟩ := ih (P j * R) U
      obtain ⟨d, hd⟩ := ih R (Q j * U)
      refine ⟨c + d, fun x ↦ ?_⟩
      have he : w (j :: l) x * ((growthEval R (p x) * s (p x)) * (growthEval U (q x) * t (q x))) =
          w l x * ((growthEval (P j * R) (p x) * s (p x)) * (growthEval U (q x) * t (q x))) +
          w l x * ((growthEval R (p x) * s (p x)) * (growthEval (Q j * U) (q x) * t (q x))) := by
        have hR : growthEval (P j * R) (p x) = (a j (p x) : ℂ) * growthEval R (p x) :=
          (map_mul (MvPolynomial.eval (elementaryGrowthVariables (p x))) _ _).trans
            (congrArg (· * growthEval R (p x)) (hP j (p x)))
        have hU : growthEval (Q j * U) (q x) = (b j (q x) : ℂ) * growthEval U (q x) :=
          (map_mul (MvPolynomial.eval (elementaryGrowthVariables (q x))) _ _).trans
            (congrArg (· * growthEval U (q x)) (hQ j (q x)))
        rw [hR, hU]
        simp only [w, List.map_cons, List.prod_cons, hab j x, Complex.ofReal_add]
        ring
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (hc x) (hd x))
  let X (s : S) (t : T) (a : Fin r → ℤ) (b : F) (u : V) :=
    s (p (elementaryCover u a b)) * t (q (elementaryCover u a b))
  have hs (s : S) (a : Fin r → ℤ) (b : F) := elementaryContDiff_hom p hp s s.property.1 a b
  have ht (t : T) (a : Fin r → ℤ) (b : F) := elementaryContDiff_hom q hq t t.property.1 a b
  have hdiff (dirs : List V) (l : List J) (s : S) (t : T) : ∃ M : ℝ, ∀ u a b,
      ‖w l (elementaryCover u a b) * iteratedFDeriv ℝ dirs.length (X s t a b) u dirs.get‖ ≤ M := by
    induction dirs using List.reverseRecOn generalizing s t with
    | nil =>
      obtain ⟨M, hM⟩ := hw l 1 1 s t
      exact ⟨M, fun u a b ↦ by simpa [X, growthEval] using hM (elementaryCover u a b)⟩
    | append_singleton dirs v ih =>
      let s' := elementarySchwartz_derivative (elementaryMapDirection p hp (elementaryOneParameter v)) s
      let t' := elementarySchwartz_derivative (elementaryMapDirection q hq (elementaryOneParameter v)) t
      obtain ⟨c, hc⟩ := ih s' t
      obtain ⟨d, hd⟩ := ih s t'
      refine ⟨c + d, fun u a b ↦ ?_⟩
      have he : (fun w ↦ fderiv ℝ (X s t a b) w v) = X s' t a b + X s t' a b := by
        funext w
        dsimp only [X, Pi.add_apply]
        rw [fderiv_fun_mul ((hs s a b).differentiable (by simp) w)
          ((ht t a b).differentiable (by simp) w)]
        simp only [add_apply, smul_apply,
          fderiv_elementaryPullback p hp, fderiv_elementaryPullback q hq, smul_eq_mul, s', t']
        ring
      rw [iteratedFDeriv_append_singleton ((hs s a b).mul (ht t a b)), he,
        iteratedFDeriv_add_apply (((hs s' a b).mul (ht t a b)).contDiffAt.of_le (mod_cast le_top))
          (((hs s a b).mul (ht t' a b)).contDiffAt.of_le (mod_cast le_top)),
        add_apply, mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hc u a b) (hd u a b))
  refine ⟨fun a b ↦ (hs s a b).mul (ht t a b), fun i ↦ ?_⟩
  let dirs : List V := (List.ofFn fun j ↦ List.replicate (i.2.1 j) (EuclideanSpace.single j 1, 0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1)).flatten
  let l : List J := (List.ofFn fun j ↦ List.replicate (i.1 j) (Sum.inl j)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.2 j) (Sum.inr j)).flatten
  obtain ⟨M, hM⟩ := hdiff dirs l s t
  refine lt_of_le_of_lt (b := ENNReal.ofReal M)
    (iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have hwgt : w l (elementaryCover u a b) =
      (∏ j, (u.1 j : ℂ) ^ i.1 j) * ∏ j, (a j : ℂ) ^ i.2.2.2 j := by
    simp only [w, l, List.map_append, List.prod_append, List.map_flatten, List.prod_flatten,
      List.map_ofFn, Function.comp_def, List.prod_ofFn, List.map_replicate, List.prod_replicate]
    rfl
  exact hwgt ▸ hM u a b

end Product
end
end Masullo
