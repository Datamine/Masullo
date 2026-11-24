/-
The lift through cofinal quotient stages adapts RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at a1d61084d11ef14e3119178113488c654be4da80
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import BruhatCosetAverage
import ElementarySchwartzFiberLift

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (K : Subgroup G) (hK : IsClosed (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]

include hK

set_option maxHeartbeats 2500000 in
private theorem bruhatCoset_lift_stage (p : BruhatSchwartzStage G)
    (Q : LCAStructuralPair (G ⧸ K))
    (hJ : Q.upper.val = p.1.upper.val.map (QuotientGroup.mk' K))
    (hC : Q.kernel = p.1.kernel.map (QuotientGroup.mk' K))
    (d : ElementaryLCAPresentation Q.StageQuotient)
    (s : ElementarySchwartz d.realDim d.torusDim d.latticeRank d.finiteFactor) :
    ∃ t : p.Space, lcaCosetIntegral K μK (p.realize t) = Q.realizeSchwartz d s := by
  letI : IsClosed (K : Set G) := hK
  letI : LocallyCompactSpace p.1.upper.val := p.1.upper.property.1.locallyCompactSpace
  letI : IsClosed (p.1.kernel.comap p.1.upper.val.subtype : Set p.1.upper.val) :=
    p.1.kernel_closed.preimage continuous_subtype_val
  letI : LocallyCompactSpace p.1.StageQuotient :=
    (QuotientGroup.isOpenQuotientMap_mk (N := p.1.kernel.comap p.1.upper.val.subtype)).locallyCompactSpace
  letI : IsClosed (Q.kernel.comap Q.upper.val.subtype : Set Q.upper.val) :=
    Q.kernel_closed.preimage continuous_subtype_val
  letI : MeasurableSpace p.1.StageQuotient := borel _
  letI : BorelSpace p.1.StageQuotient := ⟨rfl⟩
  obtain ⟨a, hao, has, ha, ν, hν, he⟩ := p.exists_cosetStage_measure K hK μK Q hJ hC
  letI := hν
  obtain ⟨t, ht⟩ := elementarySchwartz_exists_fibreLift p.2 d a hao has ν s
  refine ⟨t, funext fun y => ?_⟩
  by_cases hy : y ∈ Q.upper.val
  · have hy' : y ∈ p.1.upper.val.map (QuotientGroup.mk' K) := hJ ▸ hy
    obtain ⟨u, hu, rfl⟩ := hy'
    let x : p.1.upper.val := ⟨u, hu⟩
    let x' : Q.upper.val := ⟨QuotientGroup.mk u, hy⟩
    have heval : Q.realizeSchwartz d s x'.val = s (d.equiv (QuotientGroup.mk x')).toAdd :=
      Q.realizeSchwartz_apply_of_mem d s x'
    have hstep : s (d.equiv (a (QuotientGroup.mk x))).toAdd =
        s (d.equiv (QuotientGroup.mk x')).toAdd :=
      congrArg (fun z : Q.StageQuotient => s (d.equiv z).toAdd) (ha x hy)
    exact (he t x).trans ((ht (QuotientGroup.mk x)).trans (hstep.trans heval.symm))
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hzero (k : K) : p.realize t (x * k.val) = 0 := by
      apply p.1.realizeSchwartz_apply_of_not_mem p.2 t
      intro h
      apply hy
      rw [hJ]
      refine ⟨x * k.val, h, ?_⟩
      rw [map_mul, show QuotientGroup.mk' K k.val = 1 from
        (QuotientGroup.eq_one_iff k.val).mpr k.property, mul_one]
      rfl
    refine (lcaCosetIntegral_mk K μK (p.realize t) x).trans ?_
    refine Eq.trans ?_ (Q.realizeSchwartz_apply_of_not_mem d s _ hy).symm
    simp only [hzero, integral_zero]

set_option maxHeartbeats 2300000 in
/-- Theorem D.1.7.1(2). With any prescribed Haar measure on the closed
subgroup, coset integration is a continuous surjection. For second-countable
groups, it is open for the Schwartz–Bruhat topologies. -/
theorem exists_bruhatCosetAverage_surjective :
    letI : IsClosed (K : Set G) := hK
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz (G ⧸ K),
      (∀ f, (T f).val = lcaCosetIntegral K μK f.val) ∧
      Surjective T ∧ (SecondCountableTopology G → IsOpenQuotientMap T) := by
  letI : IsClosed (K : Set G) := hK
  obtain ⟨T, hT⟩ := exists_bruhatCosetAverage K hK μK
  have hsurj : Surjective T := by
    intro f
    obtain ⟨b, t, ht⟩ := f.property
    obtain ⟨P, Q, hJ, hC, hB⟩ := b.1.exists_cofinal_quotientPair K hK
    obtain ⟨d⟩ := Q.quotient_elementary
    obtain ⟨e⟩ := P.quotient_elementary
    let p : BruhatSchwartzStage G := ⟨P, e⟩
    obtain ⟨L, _, hL⟩ := b.1.schwartz_refinement_closedEmbedding Q hB.1 hB.2 b.2 d
    obtain ⟨s, hs⟩ := bruhatCoset_lift_stage K hK μK p Q hJ hC d (L t)
    refine ⟨p.inclusion s, Subtype.ext ?_⟩
    exact (hT (p.inclusion s)).trans (hs.trans ((hL t).trans ht))
  exact ⟨T, hT, hsurj, fun h ↦ by
    letI := h
    exact ⟨hsurj, T.continuous, bruhatSchwartz_isOpenMap_of_surjective T hsurj⟩⟩

local instance : MeasurableSpace (G ⧸ K) := borel _
local instance : BorelSpace (G ⧸ K) := ⟨rfl⟩
local instance : MeasurableSpace (PontryaginDual (G ⧸ K)) := borel _
local instance : BorelSpace (PontryaginDual (G ⧸ K)) := ⟨rfl⟩
local instance : MeasurableSpace (lcaAnnihilator K) := borel _
local instance : BorelSpace (lcaAnnihilator K) := ⟨rfl⟩

set_option maxHeartbeats 1600000 in
/-- Theorem D.1.7.1 for arbitrary closed subgroups, with Haar measures
in the compatible Weil and Plancherel normalizations. -/
theorem bruhatSchwartz_distributionalPoisson
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μK.Regular]
    (ν : Measure (G ⧸ K)) (hν : IsWeilQuotientMeasure K μ μK ν)
    (νDual : Measure (PontryaginDual (G ⧸ K))) (hνDual : IsLCAPlancherelMeasure ν νDual) :
    letI : IsClosed (K : Set G) := hK
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz (G ⧸ K),
      (∀ f, (T f).val = lcaCosetIntegral K μK f.val) ∧
      Surjective T ∧ (SecondCountableTopology G → IsOpenQuotientMap T) ∧
      ∃ e : PontryaginDual (G ⧸ K) ≃ₜ* lcaAnnihilator K,
        let νA := Measure.map e νDual
        νA.IsHaarMeasure ∧ νA.Regular ∧
        (∀ χ x, (e χ).val x = χ (QuotientGroup.mk x)) ∧
        ∀ f : BruhatSchwartz G,
          Integrable (fun χ : lcaAnnihilator K => lcaFourier μ f.val χ.val) νA ∧
          ∀ x : G, (T f).val (QuotientGroup.mk x) =
            ∫ χ : lcaAnnihilator K, lcaFourier μ f.val χ.val * (χ.val x : ℂ) ∂νA := by
  letI : IsClosed (K : Set G) := hK
  obtain ⟨T, hT, hsurj, hq⟩ := exists_bruhatCosetAverage_surjective K hK μK
  have hP (f : BruhatSchwartz G) :=
    bruhatSchwartz_poisson_closedSubgroup K hK μK μ ν hν νDual hνDual f
  obtain ⟨e, hae, hre, he, -, -⟩ := hP 0
  refine ⟨T, hT, hsurj, hq, e, hae, hre, he, fun f ↦ ?_⟩
  obtain ⟨e', _, _, he', hi, heval⟩ := hP f
  have heq : e' = e := by
    apply DFunLike.ext
    intro χ
    apply Subtype.ext
    apply PontryaginDual.ext
    intro x
    exact (he' χ x).trans (he χ x).symm
  subst e'
  exact ⟨hi, fun x ↦ (congrFun (hT f) (QuotientGroup.mk x)).trans
    ((lcaCosetIntegral_mk K μK f.val x).trans (heval x))⟩

end
end Masullo
