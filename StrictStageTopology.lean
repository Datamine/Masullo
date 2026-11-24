import StrictInductiveBounds
import TopologicalLinearLimits

open Filter Function Set Topology

namespace Masullo

noncomputable section

/-- A continuous seminorm extends across a linear topological embedding into
a locally convex space. The infimum construction removes dependence on the
algebraic retraction while retaining its values on the embedded subspace. -/
theorem exists_continuousSeminorm_extension
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (j : X →L[ℂ] Y) (hj : IsEmbedding j) (p : Seminorm ℂ X) (hp : Continuous p) :
    ∃ e : Seminorm ℂ Y, Continuous e ∧ e.comp j.toLinearMap = p := by
  let w := PolynormableSpace.withSeminorms ℂ Y
  letI : IsTopologicalAddGroup Y := w.topologicalAddGroup
  obtain ⟨s, c, _, hdom⟩ := Seminorm.bound_of_continuous
    (hj.isInducing.withSeminorms (f := j.toLinearMap) w) p hp
  let q := c • s.sup (fun r : {q : Seminorm ℂ Y // Continuous q} ↦ r.val)
  have hq : Continuous q :=
    continuous_const.mul (Seminorm.continuous_finsetSup fun r _ ↦ r.property)
  have hQ : p ≤ q.comp j.toLinearMap := by
    intro x
    simpa only [q, Seminorm.comp_apply, smul_apply, Seminorm.finset_sup_apply,
      SeminormFamily.comp_apply] using hdom x
  obtain ⟨r, hr⟩ := j.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hj.injective)
  have hLeft (x : X) : r (j x) = x := DFunLike.congr_fun hr x
  let a : Seminorm ℂ Y := p.comp r + q.comp (LinearMap.id - j.toLinearMap.comp r)
  let e := a ⊓ q
  refine ⟨e, Seminorm.continuous_of_le hq inf_le_right, ?_⟩
  ext x
  change e (j x) = p x
  apply le_antisymm
  · refine (inf_le_left (a := a) (b := q) (j x)).trans ?_
    change p (r (j x)) + q (j x - j (r (j x))) ≤ p x
    simp only [hLeft, sub_self, map_zero, add_zero, le_refl]
  · rw [show e = a ⊓ q from rfl, Seminorm.inf_apply]
    apply le_ciInf
    intro y
    change p x ≤ p (r y) + q (y - j (r y)) + q (j x - y)
    have hp' : p x ≤ p (r y) + p (x - r y) :=
      (congrArg p (add_sub_cancel ..).symm).le.trans (map_add_le_add p _ _)
    have hq' := map_add_le_add q (y - j (r y)) (j x - y)
    rw [show y - j (r y) + (j x - y) = j (x - r y) by rw [map_sub]; abel] at hq'
    have hdom' : p (x - r y) ≤ q (j (x - r y)) := hQ (x - r y)
    linarith

namespace LinearInductivePresentation

universe u v

variable {E : Type u} {F : ℕ → Type v}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)] [∀ n, TopologicalSpace (F n)]
variable [∀ n, PolynormableSpace ℂ (F n)]
variable (D : LinearInductivePresentation E F)

private theorem compatibleSeminorms_of_stage
    (hemb : ∀ n, IsEmbedding (D.transition (Nat.le_succ n))) (k : ℕ)
    (p : Seminorm ℂ (F k)) (hp : Continuous p) :
    ∃ q : ∀ n, {p : Seminorm ℂ (F n) // Continuous p},
      (q k).val = p ∧ ∀ (m n : ℕ) (h : m ≤ n) (x : F m),
        (q n).val (D.transition h x) = (q m).val x := by
  classical
  let extend (n : ℕ) (p : {p : Seminorm ℂ (F n) // Continuous p}) :
      {p : Seminorm ℂ (F (n + 1)) // Continuous p} :=
    let w := exists_continuousSeminorm_extension _ (hemb n) p.val p.property
    ⟨w.choose, w.choose_spec.1⟩
  have hext (n : ℕ) (p : {p : Seminorm ℂ (F n) // Continuous p}) (x : F n) :
      (extend n p).val (D.transition (Nat.le_succ n) x) = p.val x :=
    DFunLike.congr_fun (exists_continuousSeminorm_extension _ (hemb n) p.val p.property).choose_spec.2 x
  let below (n : ℕ) (h : n ≤ k) : {p : Seminorm ℂ (F n) // Continuous p} :=
    ⟨p.comp (D.transition h).toLinearMap, hp.comp (D.transition h).continuous⟩
  let q : ∀ n, {p : Seminorm ℂ (F n) // Continuous p} :=
    Nat.rec (below 0 (Nat.zero_le k))
      (fun n x ↦ if h : n + 1 ≤ k then below (n + 1) h else extend n x)
  have hBelow (n : ℕ) (h : n ≤ k) : q n = below n h := by
    cases n with
    | zero => rfl
    | succ n =>
      change (if h : n + 1 ≤ k then below (n + 1) h else extend n (q n)) = _
      rw [dite_eq_left h]
  have hstep (n : ℕ) (x : F n) :
      (q (n + 1)).val (D.transition (Nat.le_succ n) x) = (q n).val x := by
    by_cases h : n + 1 ≤ k
    · rw [hBelow _ h, hBelow _ ((Nat.le_succ n).trans h)]
      change p (D.transition h (D.transition (Nat.le_succ n) x)) =
        p (D.transition ((Nat.le_succ n).trans h) x)
      rw [D.transition_comp]
    · simpa only [q, dite_eq_right h] using hext n (q n) x
  refine ⟨q, ?_, fun m n h x ↦ ?_⟩
  · rw [hBelow k le_rfl]
    ext x
    exact congrArg p (D.transition_id k x)
  · induction n, h using Nat.le_induction with
    | base => rw [D.transition_id]
    | succ n h ih => rw [← D.transition_comp h (Nat.le_succ n), hstep, ih]

omit [∀ n, PolynormableSpace ℂ (F n)] in
/-- Compatible seminorms on the stages descend to a seminorm on the union. -/
theorem exists_seminorm_of_compatible
    (q : ∀ n, Seminorm ℂ (F n))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (x : F m),
      q n (D.transition h x) = q m x) :
    ∃ S : Seminorm ℂ E, ∀ n, S.comp (D.incl n).toLinearMap = q n := by
  classical
  let f (x : E) : ℝ := q (D.exhaust x).choose (D.exhaust x).choose_spec.choose
  have hf (n : ℕ) (x : F n) : f (D.incl n x) = q n x := by
    let z := D.incl n x
    let m := (D.exhaust z).choose
    let y := (D.exhaust z).choose_spec.choose
    have hy : D.incl m y = z := (D.exhaust z).choose_spec.choose_spec
    let b := max m n
    have he : D.transition (le_max_left m n) y = D.transition (le_max_right m n) x := by
      apply D.injective_incl b
      rw [D.incl_transition, D.incl_transition, hy]
    change q m y = q n x
    rw [← hc m b (le_max_left m n) y, ← hc n b (le_max_right m n) x, he]
  let S : Seminorm ℂ E :=
    { toFun := f
      map_zero' := by rw [← (D.incl 0).map_zero, hf, map_zero]
      neg' x := by
        obtain ⟨n, u, rfl⟩ := D.exhaust x
        rw [← (D.incl n).map_neg, hf, hf, map_neg_eq_map]
      add_le' x y := by
        obtain ⟨m, u, rfl⟩ := D.exhaust x
        obtain ⟨n, v, rfl⟩ := D.exhaust y
        rw [← D.incl_transition (le_max_left m n) u, ← D.incl_transition (le_max_right m n) v,
          ← map_add, hf, hf, hf]
        exact map_add_le_add _ _ _
      smul' c x := by
        obtain ⟨n, u, rfl⟩ := D.exhaust x
        rw [← map_smul, hf, hf, map_smul_eq_mul] }
  exact ⟨S, fun n ↦ DFunLike.ext _ _ (hf n)⟩

/-- Continuous seminorms extend from each stage to the countable limit. -/
theorem seminorm_extension_to_limit
    (hlimit : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p)
    (hemb : ∀ n, IsEmbedding (D.transition (Nat.le_succ n))) (k : ℕ)
    (p : Seminorm ℂ (F k)) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ q.comp (D.incl k).toLinearMap = p := by
  obtain ⟨q, hq, hc⟩ := D.compatibleSeminorms_of_stage hemb k p hp
  obtain ⟨S, hS⟩ := D.exists_seminorm_of_compatible (fun n ↦ (q n).val) hc
  refine ⟨S, hlimit S (fun n ↦ ?_), (hS k).trans hq⟩
  rw [hS]
  exact (q n).property

/-- The inclusions into a countable locally convex final limit inherit the
intrinsic stage topologies when the transition maps are embeddings. -/
theorem strict_incl_isEmbedding [IsTopologicalAddGroup E]
    (hlimit : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p)
    (hemb : ∀ n, IsEmbedding (D.transition (Nat.le_succ n))) (k : ℕ) :
    IsEmbedding (D.incl k) := by
  let e := LinearEquiv.ofInjective (D.incl k).toLinearMap (D.injective_incl k)
  have hei : Continuous e.symm := by
    let hW := PolynormableSpace.withSeminorms ℂ (F k)
    apply hW.continuous_of_continuous_comp
    intro p
    obtain ⟨q, hq, heq⟩ := D.seminorm_extension_to_limit hlimit hemb k p.val p.property
    have hcomp : p.val.comp e.symm.toLinearMap =
        q.comp (D.incl k).toLinearMap.range.subtype := by
      ext y
      rw [← heq]
      exact congrArg q (congrArg Subtype.val (e.apply_symm_apply y))
    rw [hcomp]
    exact hq.comp continuous_subtype_val
  let E₀ : _ ≃L[ℂ] _ :=
    { toLinearEquiv := e
      continuous_toFun := (D.incl k).continuous.subtype_mk _
      continuous_invFun := hei }
  exact IsEmbedding.subtypeVal.comp E₀.toHomeomorph.isEmbedding

end LinearInductivePresentation

end

end Masullo
