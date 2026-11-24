import PontryaginBidual
import PontryaginAnnihilators

/-!
# Bidual surjectivity and extensions of locally compact abelian groups
-/

open Function Topology

namespace Masullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Bidual surjectivity for a closed subgroup and for its quotient implies it for
the whole group. This uses both topological identifications in D.1.4.6. -/
theorem pontryaginBidualEval_surjective_of_subgroup_and_quotient
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H]
    (hSub : Surjective (pontryaginBidualEval (G := H)))
    (hQuot : Surjective (pontryaginBidualEval (G := G ⧸ H))) :
    Surjective (pontryaginBidualEval (G := G)) := by
  let J := lcaAnnihilator H
  obtain ⟨eQ, heQ⟩ := lcaQuotientDual_equiv_annihilator H hH
  obtain ⟨eH, heH⟩ := lcaDualQuotient_equiv_subgroupDual H hH
  let incl : J →ₜ* PontryaginDual G := ⟨J.subtype, continuous_subtype_val⟩
  let q : PontryaginDual G →ₜ* (PontryaginDual G ⧸ J) :=
    ⟨QuotientGroup.mk' J, QuotientGroup.continuous_mk⟩
  intro η
  obtain ⟨a, ha⟩ := hQuot (η.comp (incl.comp ⟨eQ.toMonoidHom, eQ.continuous⟩))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  let δ := η / pontryaginBidualEval x
  have hJ : J ≤ δ.toMonoidHom.ker := by
    intro χ hχ
    obtain ⟨ψ, hψ⟩ := eQ.surjective ⟨χ, hχ⟩
    have hval (y : G) : χ y = ψ (QuotientGroup.mk y) := by
      rw [← heQ ψ y, hψ]
    have hη : η χ = ψ (QuotientGroup.mk x) := by
      have h := DFunLike.congr_fun ha ψ
      change ψ (QuotientGroup.mk x) = η (eQ ψ).val at h
      rw [hψ] at h
      exact h.symm
    change η χ / χ x = 1
    rw [hη, hval, div_self']
  let f := QuotientGroup.lift J δ.toMonoidHom hJ
  have hf : Continuous f := (QuotientGroup.isQuotientMap_mk J).continuous_iff.mpr δ.continuous
  let δQ : PontryaginDual (PontryaginDual G ⧸ J) := ⟨f, hf⟩
  obtain ⟨y, hy⟩ := hSub (δQ.comp ⟨eH.symm.toMonoidHom, eH.symm.continuous⟩)
  refine ⟨x * y.val, PontryaginDual.ext fun χ ↦ ?_⟩
  have hh := DFunLike.congr_fun hy (eH (q χ))
  change eH (q χ) y = δQ (eH.symm (eH (q χ))) at hh
  rw [eH.symm_apply_apply] at hh
  have heval : χ y.val = η χ / χ x := (heH χ y).symm.trans hh
  change χ (x * y.val) = η χ
  rw [map_mul, heval, mul_comm, div_mul_cancel]

/-- In particular, evaluation identifies a locally compact abelian group with its
bidual whenever it has a compact open subgroup. -/
theorem pontryaginBidualEval_surjective_of_compactOpenSubgroup
    (H : Subgroup G) (hC : IsCompact (H : Set G)) (hO : IsOpen (H : Set G)) :
    Surjective (pontryaginBidualEval (G := G)) := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hC
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hO
  exact pontryaginBidualEval_surjective_of_subgroup_and_quotient H (H.isClosed_of_isOpen hO)
    pontryaginBidualEval_surjective_of_compact pontryaginBidualEval_surjective_of_discrete

end Masullo
