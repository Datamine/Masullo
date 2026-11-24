import BruhatStageLogSeminorms
import ModulationSection

open Function Module Set Topology

namespace Masullo.WholeBruhatStage

noncomputable section

/-- A normalized radial vector extends to a basis with every other vector in the kernel. -/
theorem exists_radial_basis {X : Type*} [AddCommGroup X] [Module ℝ X]
    [Module.Finite ℝ X] (L : X →ₗ[ℝ] ℝ) (v : X) (hv : L v = 1)
    {n : ℕ} (hn : Module.finrank ℝ X = n + 1) :
    ∃ B : Basis (Fin (n + 1)) ℝ X, B 0 = v ∧ ∀ j : Fin n, L (B j.succ) = 0 := by
  let T : ℝ × L.ker →ₗ[ℝ] X :=
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v).coprod L.ker.subtype
  have hT (p : ℝ × L.ker) : T p = p.1 • v + p.2.val := rfl
  have hLT (p : ℝ × L.ker) : L (T p) = p.1 := by
    rw [hT, map_add, map_smul, hv, smul_eq_mul, mul_one,
      show L p.2.val = 0 from p.2.property, add_zero]
  have hinj : Injective T := by
    intro p q h
    have hfirst : p.1 = q.1 := by simpa only [hLT] using congrArg L h
    have hsecond : p.2 = q.2 := by
      apply Subtype.ext
      rw [hT, hT, hfirst] at h
      exact add_left_cancel h
    exact Prod.ext hfirst hsecond
  have hsurj : Surjective T := by
    intro x
    have hx : x - (L x) • v ∈ L.ker := by
      change L (x - (L x) • v) = 0
      rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    refine ⟨(L x, ⟨x - (L x) • v, hx⟩), ?_⟩
    rw [hT, add_sub_cancel]
  let e := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  have hdim := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, hn] at hdim
  let C := Module.finBasisOfFinrankEq (R := ℝ) (M := L.ker) (n := n) (by omega)
  let i : Fin (n + 1) ≃ PUnit.{1} ⊕ Fin n := (finSuccEquiv n).trans
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _))
  let B := (((Basis.singleton PUnit.{1} ℝ).prod C).map e).reindex i.symm
  refine ⟨B, ?_, fun j => ?_⟩
  · have hi : i 0 = Sum.inl PUnit.unit := by simp [i]
    rw [show B 0 = e (1, 0) by simp [B, hi, Basis.prod_apply]]
    change T (1, 0) = v
    rw [hT]
    simp
  · have hi : i j.succ = Sum.inr j := by simp [i]
    rw [show B j.succ = e (0, C j) by simp [B, hi, Basis.prod_apply]]
    exact hLT (0, C j)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

set_option maxHeartbeats 1200000 in
/-- For each whole-group elementary stage, an arbitrary radial section
can be completed by norm-one one-parameter directions on the original group.
Their projections form a basis, with one angular direction for each torus
coordinate of this stage. -/
theorem exists_radial_angular_basis (P : WholeBruhatStage G)
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m) :
    ∃ (B : Basis (Fin (P.val.2.torusDim + 1)) ℝ
        (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
      (γ : Fin (P.val.2.torusDim + 1) → Multiplicative ℝ →ₜ* G),
      γ 0 = τ ∧ (∀ (j : Fin P.val.2.torusDim) t, m (γ j.succ t) = 1) ∧
      ∀ j, P.coordinates.comp (γ j) = elementaryOneParameter (B j) := by
  let X := EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)
  let L₀ : X →+ ℝ := (P.logCoordinate m).comp elementaryCoverHom
  let L := L₀.toRealLinearMap ((P.logCoordinate_isProperMap m hm).continuous.comp
    elementaryCoverHom_continuous)
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift (P.coordinates.comp τ)
  have hrad (t : ℝ) : L (t • v) = t := by
    change P.logCoordinate m (elementaryCoverHom (t • v)) = t
    rw [← hv t]
    exact (P.logCoordinate_coordinates m (τ (Multiplicative.ofAdd t))).trans
      (congrArg Multiplicative.toAdd (hτ (Multiplicative.ofAdd t)))
  have hL : L v = 1 := by simpa only [one_smul] using hrad 1
  have hreal := (P.logCoordinate_dimensions m hm hτ.surjective).1
  have hdim : Module.finrank ℝ X = P.val.2.torusDim + 1 := by
    rw [show Module.finrank ℝ X = P.val.2.realDim + P.val.2.torusDim by
      simp only [X, Module.finrank_prod, finrank_euclideanSpace_fin], hreal, Nat.add_comm]
  obtain ⟨B, hB, hBker⟩ := exists_radial_basis L v hL hdim
  letI : T2Space P.val.2.finiteFactor := DiscreteTopology.toT2Space
  letI : T2Space P.ElementaryCoordinates := Prod.t2Space
  letI : T2Space (Multiplicative P.ElementaryCoordinates) :=
    inferInstanceAs (T2Space P.ElementaryCoordinates)
  choose a ha using fun j : Fin P.val.2.torusDim =>
    exists_oneParameter_lift_proper P.coordinates (P.coordinates_proper m hm)
      P.coordinates_surjective (elementaryOneParameter (B j.succ))
  refine ⟨B, Fin.cons τ a, Fin.cons_zero _ _, ?_, ?_⟩
  · intro j t
    apply Multiplicative.toAdd.injective
    rw [Fin.cons_succ, ← P.logCoordinate_coordinates]
    have h := DFunLike.congr_fun (ha j) t
    change P.coordinates (a j t) = Multiplicative.ofAdd (elementaryCoverHom (t.toAdd • B j.succ)) at h
    rw [h]
    change L (t.toAdd • B j.succ) = 0
    have hj : L (B j.succ) = 0 := hBker j
    rw [map_smul, hj, smul_zero]
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.cons_zero, hB]
      exact ContinuousMonoidHom.ext fun t => Multiplicative.toAdd.injective (hv t.toAdd)
    · simpa only [Fin.cons_succ] using ha i

end
end Masullo.WholeBruhatStage
