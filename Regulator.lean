import Mathlib.Algebra.Module.NatInt
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open Module NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Set
open scoped Classical

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

/-- The logarithmic norm-zero hyperplane in the coordinates of (A.2.3.5). -/
def regulatorHyperplane : Submodule ℝ (InfinitePlace F → ℝ) :=
  (∑ v : InfinitePlace F, LinearMap.proj v).ker

theorem mem_regulatorHyperplane (x : InfinitePlace F → ℝ) :
    x ∈ regulatorHyperplane F ↔ ∑ v, x v = 0 := by
  classical
  simp [regulatorHyperplane, LinearMap.sum_apply]

/-- Dropping the distinguished coordinate identifies the hyperplane with the
coordinates of Mathlib's logarithmic unit embedding. -/
def regulatorHyperplaneEquiv : regulatorHyperplane F ≃L[ℝ] logSpace F := by
  classical
  apply LinearEquiv.toContinuousLinearEquiv
  let L : regulatorHyperplane F →ₗ[ℝ] logSpace F :=
    { toFun := fun x v => x.val v
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro x y hxy
    have hx := (mem_regulatorHyperplane F x.val).mp x.property
    have hy := (mem_regulatorHyperplane F y.val).mp y.property
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)] at hx hy
    have hcoord (v : {v : InfinitePlace F // v ≠ w₀}) : x.val v = y.val v :=
      congrFun hxy v
    have hs : (∑ v : {v : InfinitePlace F // v ≠ w₀}, x.val v) =
        ∑ v : {v : InfinitePlace F // v ≠ w₀}, y.val v :=
      Finset.sum_congr rfl fun v _ => hcoord v
    apply Subtype.ext
    funext v
    by_cases hv : v = w₀
    · subst v
      linarith
    · exact hcoord ⟨v, hv⟩
  · intro y
    let x (v : InfinitePlace F) :=
      if hv : v ≠ w₀ then y ⟨v, hv⟩ else -∑ i, y i
    have hx : x ∈ regulatorHyperplane F := by
      rw [mem_regulatorHyperplane, Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)]
      have hsum : (∑ v : {v : InfinitePlace F // v ≠ w₀}, x v.val) = ∑ v, y v :=
        Finset.sum_congr rfl fun v _ => by simp [x, v.property]
      rw [hsum]
      simp [x]
    refine ⟨⟨x, hx⟩, ?_⟩
    funext v
    change x v = y v
    simp [x, v.property]

/-- The regulator in coordinates omitting one infinite place agrees with the
restriction of the full log-norm map. -/
theorem regulator_coordinates (u : (𝓞 F)ˣ) :
    ∃ x : regulatorHyperplane F,
      (∀ v, x.val v = (v.mult : ℝ) * Real.log (v (u : F))) ∧
      regulatorHyperplaneEquiv F x = logEmbedding F (Additive.ofMul u) := by
  let x := fun v : InfinitePlace F => (v.mult : ℝ) * Real.log (v (u : F))
  have hx : x ∈ regulatorHyperplane F :=
    (mem_regulatorHyperplane F x).mpr (sum_mult_mul_log u)
  exact ⟨⟨x, hx⟩, fun _ => rfl, rfl⟩

/-- The real basis associated to the fundamental units in (A.2.3.9). -/
def regulatorBasis : Basis (Fin (NumberField.Units.rank F)) ℝ (logSpace F) :=
  (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)

theorem regulatorBasis_span :
    Submodule.span ℤ (Set.range (regulatorBasis F)) = unitLattice F :=
  (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)

/-- The closed and discrete image, kernel, and unit rank of Lemma A.2.3.4,
together with the compactness of the quotient by the regulator lattice. -/
theorem regulator_lattice :
    IsClosed (unitLattice F : Set (logSpace F)) ∧
    Nonempty (DiscreteTopology (unitLattice F)) ∧
    CompactSpace (logSpace F ⧸ unitLattice F) ∧
    (logEmbedding F).ker = (torsion F).toAddSubgroup ∧
    Finite (torsion F) ∧ IsCyclic (torsion F) ∧
    (rootsOfUnity (torsionOrder F) (𝓞 F) = torsion F) ∧
    Monoid.FG (𝓞 F)ˣ := by
  classical
  letI : DiscreteTopology (unitLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (unitLattice F))
  have hclosed : IsClosed (unitLattice F : Set (logSpace F)) :=
    AddSubgroup.isClosed_of_discrete (H := (unitLattice F).toAddSubgroup)
  have hcompact : CompactSpace (logSpace F ⧸ unitLattice F) := by
    let π := (unitLattice F).mkQ
    let b := regulatorBasis F
    have hb : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
      (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
    have hsurj : π '' closure (ZSpan.fundamentalDomain b) = univ := by
      apply eq_univ_of_forall
      intro q
      obtain ⟨x, rfl⟩ := (unitLattice F).mkQ_surjective q
      obtain ⟨v, hv, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
      have hvl : (v : logSpace F) ∈ unitLattice F := (regulatorBasis_span F) ▸ v.property
      refine ⟨v +ᵥ x, subset_closure hv, ?_⟩
      change π (v.val + x) = π x
      have hvzero : π v.val = 0 := (Submodule.Quotient.mk_eq_zero (p := unitLattice F)).mpr hvl
      rw [map_add, hvzero, zero_add]
    exact ⟨hsurj ▸ hb.image continuous_quot_mk⟩
  exact ⟨hclosed, ⟨inferInstance⟩, hcompact, logEmbedding_ker, inferInstance,
    inferInstance, rootsOfUnity_eq_torsion F, inferInstance⟩

/-- The unit quotient is free of rank one less than the number of infinite places. -/
def regulatorUnitBasis := basisModTorsion F

/-- The signed parallelotope in Lemma A.2.3.5 has compact closure, nonempty
interior, and exactly one translate through each point. -/
theorem regulator_fundamentalDomain :
    IsCompact (closure (ZSpan.fundamentalDomain (regulatorBasis F))) ∧
    (interior (ZSpan.fundamentalDomain (regulatorBasis F))).Nonempty ∧
    ∀ x : logSpace F, ∃! v : unitLattice F,
      v +ᵥ x ∈ ZSpan.fundamentalDomain (regulatorBasis F) := by
  classical
  let b := regulatorBasis F
  refine ⟨(ZSpan.fundamentalDomain_isBounded b).isCompact_closure, ?_, ?_⟩
  · let U : Set (logSpace F) := ⋂ i, (b.coord i) ⁻¹' Ioo (0 : ℝ) 1
    have hopen : IsOpen U := isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage (LinearMap.continuous_of_finiteDimensional (b.coord i))
    have hU : U ⊆ ZSpan.fundamentalDomain b := by
      intro x hx
      rw [ZSpan.mem_fundamentalDomain]
      intro i
      exact Ioo_subset_Ico_self (Set.mem_iInter.mp hx i)
    refine ⟨b.equivFun.symm (fun _ => 1 / 2), interior_maximal hU hopen ?_⟩
    apply Set.mem_iInter.mpr
    intro i
    change b.equivFun (b.equivFun.symm (fun _ => 1 / 2)) i ∈ Ioo 0 1
    rw [LinearEquiv.apply_symm_apply]
    norm_num
  · intro x
    rw [← regulatorBasis_span F]
    exact ZSpan.exist_unique_vadd_mem_fundamentalDomain b x

end Masullo
