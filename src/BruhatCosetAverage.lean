import BruhatPoisson
import ElementarySchwartzFiberAverage

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (K : Subgroup G) (hK : IsClosed (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]

local instance : MeasurableSpace (G ⧸ K) := borel _
local instance : BorelSpace (G ⧸ K) := ⟨rfl⟩

include hK

set_option maxHeartbeats 1400000 in
/-- The fibre measure on the kernel of the induced elementary stage map
computes the ambient coset integral on each coset through the open upper subgroup. -/
theorem BruhatSchwartzStage.exists_cosetStage_measure (p : BruhatSchwartzStage G)
    (Q : LCAStructuralPair (G ⧸ K))
    (hJ : Q.upper.val = p.1.upper.val.map (QuotientGroup.mk' K))
    (hC : Q.kernel = p.1.kernel.map (QuotientGroup.mk' K)) :
    letI : MeasurableSpace p.1.StageQuotient := borel _
    ∃ a : p.1.StageQuotient →ₜ* Q.StageQuotient,
      IsOpenMap a ∧ Surjective a ∧
      (∀ (x : p.1.upper.val) (hx : QuotientGroup.mk x.val ∈ Q.upper.val),
        a (QuotientGroup.mk x) = QuotientGroup.mk ⟨QuotientGroup.mk x.val, hx⟩) ∧
      ∃ ν : Measure a.toMonoidHom.ker, ν.IsHaarMeasure ∧
        ∀ (s : p.Space) (x : p.1.upper.val),
          lcaCosetIntegral K μK (p.realize s) (QuotientGroup.mk x.val) =
            ∫ k : a.toMonoidHom.ker,
              s (p.2.equiv (QuotientGroup.mk x * k.val)).toAdd ∂ν := by
  let J := p.1.upper.val
  let N := p.1.kernel.comap J.subtype
  let A := p.1.StageQuotient
  letI : IsClosed (N : Set J) := p.1.kernel_closed.preimage continuous_subtype_val
  letI : LocallyCompactSpace J := p.1.upper.property.1.locallyCompactSpace
  letI : BorelSpace A := ⟨rfl⟩
  let π : J →ₜ* A := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  have hN : IsCompact (N : Set J) := by
    apply (J.isClosed_of_isOpen p.1.upper.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage
      (K := (p.1.kernel : Set G))
    rw [← lcaDualAnnihilator_annihilator p.1.kernel p.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ p.1.annihilator_open
  have hp : IsProperMap π := (lcaQuotient_isProper_iff N).mpr hN
  obtain ⟨a, hao, has, haK, ha⟩ := p.1.exists_quotientStageMap K Q hJ hC
  obtain ⟨ν, hν, -, he⟩ := exists_haar_imageFiber_integral K J hK p.1.upper.property.1 π hp
    μK a.toMonoidHom.ker haK
  refine ⟨a, hao, has, ha, ν, hν, fun s x => ?_⟩
  let g (y : A) := s (p.2.equiv y).toAdd
  have hg : Continuous g := by
    have hs : Continuous (p.realize s) := bruhatSchwartz_continuous (p.inclusion s)
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact (hs.comp continuous_subtype_val).congr (p.1.realizeSchwartz_apply_of_mem p.2 s)
  exact (lcaCosetIntegral_mk K μK (p.realize s) x.val).trans
    ((he hg (p.1.realizeSchwartz_apply_of_not_mem p.2 s)
      (p.1.realizeSchwartz_apply_of_mem p.2 s) x).2)

set_option maxHeartbeats 7500000 in
private theorem bruhatCoset_stage (p : BruhatSchwartzStage G) :
    ∃ q : BruhatSchwartzStage (G ⧸ K),
      (∀ s : p.Space, ∃ t : q.Space, q.realize t = lcaCosetIntegral K μK (p.realize s)) ∧
      ∃ Q : Seminorm ℂ p.Space, Continuous Q ∧
        ∀ s y, ‖lcaCosetIntegral K μK (p.realize s) y‖ ≤ Q s := by
  letI : IsClosed (K : Set G) := hK
  obtain ⟨P, hJ, hC⟩ := p.1.exists_quotientPair K hK
  obtain ⟨d⟩ := P.quotient_elementary
  let q : BruhatSchwartzStage (G ⧸ K) := ⟨P, d⟩
  letI : LocallyCompactSpace p.1.upper.val := p.1.upper.property.1.locallyCompactSpace
  letI : IsClosed (p.1.kernel.comap p.1.upper.val.subtype : Set p.1.upper.val) :=
    p.1.kernel_closed.preimage continuous_subtype_val
  letI : LocallyCompactSpace p.1.StageQuotient :=
    (QuotientGroup.isOpenQuotientMap_mk (N := p.1.kernel.comap p.1.upper.val.subtype)).locallyCompactSpace
  letI : IsClosed (P.kernel.comap P.upper.val.subtype : Set P.upper.val) :=
    P.kernel_closed.preimage continuous_subtype_val
  letI : MeasurableSpace p.1.StageQuotient := borel _
  letI : BorelSpace p.1.StageQuotient := ⟨rfl⟩
  obtain ⟨a, hao, has, ha, ν, hν, he⟩ := p.exists_cosetStage_measure K hK μK P hJ hC
  letI := hν
  have hClosed : IsClosed (a.toMonoidHom.ker : Set p.1.StageQuotient) :=
    isClosed_singleton.preimage a.continuous
  obtain ⟨S, hS, hSb⟩ := elementarySchwartz_fibreIntegral_seminorm p.2
    a.toMonoidHom.ker hClosed ν
  have hz (s : p.Space) (y : G ⧸ K) (hy : y ∉ P.upper.val) :
      lcaCosetIntegral K μK (p.realize s) y = 0 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine (lcaCosetIntegral_mk K μK (p.realize s) x).trans ?_
    have hzero (k : K) : p.realize s (x * k.val) = 0 := by
      apply p.1.realizeSchwartz_apply_of_not_mem p.2 s
      intro h
      apply hy
      rw [hJ]
      refine ⟨x * k.val, h, ?_⟩
      rw [map_mul, show QuotientGroup.mk' K k.val = 1 from
        (QuotientGroup.eq_one_iff k.val).mpr k.property, mul_one]
      rfl
    simp only [hzero, integral_zero]
  have hrep {y : G ⧸ K} (hy : y ∈ P.upper.val) :
      ∃ x : p.1.upper.val, QuotientGroup.mk x.val = y := by
    rw [hJ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨q, ?_, S, hS, ?_⟩
  · intro s
    obtain ⟨t, ht⟩ := elementarySchwartz_exists_fibreAverage p.2 d a hao has ν s
    refine ⟨t, funext fun y => ?_⟩
    by_cases hy : y ∈ P.upper.val
    · obtain ⟨x, rfl⟩ := hrep hy
      let x' : P.upper.val := ⟨QuotientGroup.mk x.val, hy⟩
      have heval : P.realizeSchwartz d t x'.val = t (d.equiv (QuotientGroup.mk x')).toAdd :=
        P.realizeSchwartz_apply_of_mem d t x'
      have hstep : t (d.equiv (QuotientGroup.mk x')).toAdd =
          t (d.equiv (a (QuotientGroup.mk x))).toAdd :=
        congrArg (fun z : P.StageQuotient => t (d.equiv z).toAdd) (ha x hy).symm
      exact heval.trans (hstep.trans ((ht (QuotientGroup.mk x)).trans (he s x).symm))
    · exact (P.realizeSchwartz_apply_of_not_mem d t y hy).trans (hz s y hy).symm
  · intro s y
    by_cases hy : y ∈ P.upper.val
    · obtain ⟨x, rfl⟩ := hrep hy
      exact (congrArg (fun z : ℂ => ‖z‖) (he s x)).le.trans (hSb s (QuotientGroup.mk x))
    · exact ((congrArg (fun z : ℂ => ‖z‖) (hz s y hy)).trans norm_zero).le.trans (apply_nonneg S s)

/-- Coset integration as a complex-linear map before imposing the target topology. -/
def bruhatCosetLinear : BruhatSchwartz G →ₗ[ℂ] ((G ⧸ K) → ℂ) where
  toFun f := lcaCosetIntegral K μK f.val
  map_add' f g := by
    funext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    change lcaCosetIntegral K μK (f.val + g.val) (QuotientGroup.mk x) = _
    simp only [Pi.add_apply, lcaCosetIntegral_mk K μK]
    exact integral_add ((bruhatSchwartz_coset_integrable_continuous K hK μK f).1 x)
      ((bruhatSchwartz_coset_integrable_continuous K hK μK g).1 x)
  map_smul' c f := by
    funext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    change lcaCosetIntegral K μK (c • f.val) (QuotientGroup.mk x) = _
    simp only [Pi.smul_apply, RingHom.id_apply, lcaCosetIntegral_mk K μK, integral_smul]

set_option maxHeartbeats 6000000 in
/-- Coset integration maps the full physical Schwartz–Bruhat space
continuously into the full quotient Schwartz–Bruhat space. -/
theorem exists_bruhatCosetAverage :
    letI : IsClosed (K : Set G) := hK
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz (G ⧸ K),
      ∀ f, (T f).val = lcaCosetIntegral K μK f.val := by
  letI : IsClosed (K : Set G) := hK
  let L := bruhatCosetLinear K hK μK
  have hA (y : G ⧸ K) : Continuous (fun f : BruhatSchwartz G => L f y) := by
    let A := (LinearMap.proj y).comp L
    apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G => p.inclusion) A).mpr
    intro p
    obtain ⟨q, -, S, hS, hSb⟩ := bruhatCoset_stage K hK μK p
    let B := A.comp p.inclusion
    change Continuous B
    apply continuous_of_continuousAt_zero B
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun f => hSb f y) (map_zero S ▸ hS.tendsto 0)
  let eval (y : G ⧸ K) : BruhatSchwartz G →L[ℂ] ℂ :=
    ⟨(LinearMap.proj y).comp L, hA y⟩
  have hstage (p : BruhatSchwartzStage G) :
      ∃ (q : BruhatSchwartzStage (G ⧸ K)) (B : p.Space →L[ℂ] q.Space),
        ∀ s y, q.realize (B s) y = eval y (p.inclusion s) := by
    obtain ⟨q, hq, -⟩ := bruhatCoset_stage K hK μK p
    let r : G ⧸ K → G ⧸ K := id
    let E (y : G ⧸ K) : p.Space →L[ℂ] ℂ := (eval y).comp p.inclusionCLM
    have hr (s : p.Space) : ∃ t : q.Space, ∀ y, q.realize t (r y) = E y s := by
      obtain ⟨t, ht⟩ := hq s
      exact ⟨t, fun y => congrFun ht y⟩
    have hex := bruhatStage_exists_clm_of_evaluation (G := G) (H := G ⧸ K)
      (X := G ⧸ K) p q r Function.surjective_id E hr
    obtain ⟨B, hB⟩ := hex
    exact ⟨q, B, hB⟩
  obtain ⟨T, hT⟩ := bruhatSchwartz_exists_clm_of_stage_evaluation (H := G ⧸ K)
    id Function.surjective_id eval hstage
  exact ⟨T, fun f => funext (hT f)⟩

end
end Masullo
