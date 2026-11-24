import SUnitLogLattice
import SUnitRank
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

open IsDedekindDomain NumberField NumberField.Units Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

set_option maxHeartbeats 450000 in
/-- The discrete S-unit logs span the reduced real log space. -/
theorem sUnitReducedLog_isZLattice (S : Finset (Place F)) :
    IsZLattice ℝ (LinearMap.range (sUnitReducedLog F S)) := by
  let f := sUnitReducedLog F S
  letI : DiscreteTopology f.range := sUnitReducedLog_image_discrete F S
  letI := sUnits_finite F S
  letI : Finite f.ker := by
    letI := (sUnitReducedLog_ker_finite F S).to_subtype
    let e (x : f.ker) : {u : (sIntegerRing F S)ˣ | sUnitReducedLog F S (Additive.ofMul u) = 0} :=
      ⟨x.val.toMul, x.property⟩
    exact Finite.of_injective e (fun _ _ h => Subtype.ext (congrArg Subtype.val h))
  have hT : Module.IsTorsion ℤ f.ker := by
    intro x
    obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp (isOfFinAddOrder_of_finite x)
    exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, hx⟩
  have he := congrArg Cardinal.toNat f.rank_range_add_rank_ker
  rw [hT.rank_eq_zero, add_zero] at he
  change Module.finrank ℤ f.range = Module.finrank ℤ (Additive (sIntegerRing F S)ˣ) at he
  refine ⟨Submodule.eq_top_of_finrank_eq ?_⟩
  let V := ReducedSLogIndex F S → ℝ
  let s : Set V := f.range
  have hspan : Submodule.span ℤ s = f.range := Submodule.span_eq f.range
  have hdisc : DiscreteTopology (Submodule.span ℤ s) :=
    hspan.symm ▸ sUnitReducedLog_image_discrete F S
  have h : Module.finrank ℝ (Submodule.span ℝ s) =
      Module.finrank ℤ (Submodule.span ℤ s) :=
    Real.finrank_eq_int_finrank_of_discrete (s := s) hdisc
  rw [hspan, he, sUnits_finrank] at h
  rw [Module.finrank_fintype_fun_eq_card, card_reducedSLogIndex, Fintype.card_sum, Fintype.card_coe]
  exact h


end

end Masullo
