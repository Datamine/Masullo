import PrincipalValueStageEmbedding
import HomogeneousThetaStructure
import SLocalArchRangeComparison

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := SLocalThetaQuotient F S
private abbrev K := SLocalThetaNormOne F S
private abbrev Test := sLocalBruhatImage F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

private theorem component_principal_range (W : Finset S) (ω : PontryaginDual (K F S)) :
    range ((sLocalThetaToComponent F S ν ω).comp (sLocalThetaPrincipalValues F S W)) =
      ((sLocalFiniteNonzeroTestSubspace F S W).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ :
        Set (SLocalHomogeneousThetaQuotient F S ν ω)) := by
  rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
  ext y
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F S).ker q
    refine ⟨sLocalWeilPrincipalValues F S W f, ⟨f,rfl⟩, ?_⟩
    change _ = sLocalThetaToComponent F S ν ω (sLocalThetaPrincipalValues F S W
      (Submodule.Quotient.mk f))
    rw [sLocalThetaPrincipalValues_mk]
    rfl
  · rintro ⟨_,⟨f,rfl⟩,rfl⟩
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    change sLocalThetaToComponent F S ν ω (sLocalThetaPrincipalValues F S W
      (Submodule.Quotient.mk f)) = _
    rw [sLocalThetaPrincipalValues_mk]
    rfl

private theorem section_component_principal_mem_range (W : Finset S)
    (ω : PontryaginDual (K F S))
    (s : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] E F S)
    (hp : ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q)
        ((ν.real univ : ℂ) • s (sLocalThetaToComponent F S ν ω q)))
    (q : E F S)
    (hq : sLocalThetaToComponent F S ν ω q ∈
      ((sLocalFiniteNonzeroTestSubspace F S W).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ :
        Set (SLocalHomogeneousThetaQuotient F S ν ω))) :
    s (sLocalThetaToComponent F S ν ω q) ∈ range (sLocalThetaPrincipalValues F S W) := by
  let P := sLocalThetaPrincipalValues F S W
  let A := s.comp (sLocalThetaToComponent F S ν ω)
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  let z : ℂ := ν.real univ
  have hz : z ≠ 0 := by
    have h := Measure.measure_pos_of_nonempty_interior (s := (univ : Set (K F S))) ν (by simp)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos h.ne' (measure_ne_top _ _)).ne'
  rw [← component_principal_range F S ν W ω] at hq
  obtain ⟨y,hy⟩ := hq
  change sLocalThetaToComponent F S ν ω (P y) = sLocalThetaToComponent F S ν ω q at hy
  have he := sLocalWeilPrincipalValuesQuotient_average F S W ν ω P (z • A)
    (sLocalThetaPrincipalValues_mk F S W) hp y
  change P (z • A y) = z • A (P y) at he
  rw [map_smul] at he
  have hc : P (A y) = A (P y) := by
    simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using congrArg (z⁻¹ • ·) he
  exact ⟨A y, hc.trans (congrArg s hy)⟩

/-- A character component vanishes when the class is an eigenvector of
one norm-one translation with a different eigenvalue. -/
theorem sLocalThetaToComponent_eq_zero_of_eigenvalue_ne
    (ω : PontryaginDual (K F S)) (u : E F S) (k : K F S) (z : ℂ)
    (hk : (ω k : ℂ) ≠ z) (hu : sLocalNormOneAction F S k u = z • u) :
    sLocalThetaToComponent F S ν ω u = 0 := by
  obtain ⟨_,_,_,hker,_,_⟩ := sLocalThetaComponent_pettisSection F S ν ω
  let C := sLocalThetaToComponent F S ν ω
  have hmem : u - (((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k u ∈ C.ker := by
    rw [hker]
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨(k,u),rfl⟩
  have hz : C (u - (((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k u) = 0 :=
    LinearMap.mem_ker.mp hmem
  rw [hu, map_sub, map_smul, map_smul, smul_smul] at hz
  have hz' : 1 - (((ω k)⁻¹ : Circle) : ℂ) * z ≠ 0 := by
    intro h
    apply hk
    have hh := congrArg ((ω k : ℂ) * ·) (sub_eq_zero.mp h)
    rw [Circle.coe_inv, mul_one, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul] at hh
    exact hh
  have hz'' : (1 - (((ω k)⁻¹ : Circle) : ℂ) * z) • C u = 0 := by
    rw [sub_smul, one_smul]
    exact hz
  exact (smul_eq_zero.mp hz'').resolve_left hz'

private theorem component_zero_of_other_isotype
    (ω τ : PontryaginDual (K F S)) (hne : ω ≠ τ) (u : E F S)
    (hu : ∀ k, sLocalNormOneAction F S k u = (τ k : ℂ) • u) :
    sLocalThetaToComponent F S ν ω u = 0 := by
  obtain ⟨k,hk⟩ : ∃ k : K F S, (ω k : ℂ) ≠ (τ k : ℂ) := by
    by_contra! h
    exact hne (DFunLike.ext _ _ fun k ↦ Subtype.ext (h k))
  exact sLocalThetaToComponent_eq_zero_of_eigenvalue_ne F S ν ω u k (τ k) hk (hu k)

/-- The ordinary principal-value range contains every finitely supported
character family that satisfies the homogeneous range conditions. -/
theorem sLocalTheta_mem_principalRange_of_finite_components
    (W : Finset S) (q : E F S) (A : Finset (PontryaginDual (K F S)))
    (hzero : ∀ ω ∉ A, sLocalThetaToComponent F S ν ω q = 0)
    (hq : ∀ ω ∈ A, sLocalThetaToComponent F S ν ω q ∈
      ((sLocalFiniteNonzeroTestSubspace F S W).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ :
        Set (SLocalHomogeneousThetaQuotient F S ν ω))) :
    q ∈ range (sLocalThetaPrincipalValues F S W) := by
  let h (ω : PontryaginDual (K F S)) := sLocalThetaComponent_pettisSection F S ν ω
  let s (ω : PontryaginDual (K F S)) := (h ω).choose
  let P := sLocalThetaPrincipalValues F S W
  let u (ω : PontryaginDual (K F S)) := s ω (sLocalThetaToComponent F S ν ω q)
  have he : ∑ ω ∈ A, u ω = q := by
    apply sLocalThetaToAllComponents_injective F S ν
    funext ω
    change sLocalThetaToComponent F S ν ω (∑ τ ∈ A, u τ) = _
    rw [map_sum, Finset.sum_eq_single ω]
    · exact (h ω).choose_spec.1 _
    · intro τ _ hne
      exact component_zero_of_other_isotype F S ν ω τ hne.symm (u τ) ((h τ).choose_spec.2.1 _)
    · intro hω
      change sLocalThetaToComponent F S ν ω (s ω (sLocalThetaToComponent F S ν ω q)) = 0
      rw [(h ω).choose_spec.1 _, hzero ω hω]
  have hmem : ∑ ω ∈ A, u ω ∈ P.toLinearMap.range := by
    apply Submodule.sum_mem
    intro ω hω
    exact section_component_principal_mem_range F S ν W ω (s ω)
      (h ω).choose_spec.2.2.2.2 q (hq ω hω)
  exact he ▸ hmem

variable [ν.WeaklyRegular]

/-- If each norm-one character component belongs to its homogeneous
principal-value range, the ordinary class lies in the closure of the
actual ordinary principal-value range. -/
theorem sLocalTheta_mem_closure_principalRange_of_components (W : Finset S) (q : E F S)
    (hq : ∀ ω, sLocalThetaToComponent F S ν ω q ∈
      ((sLocalFiniteNonzeroTestSubspace F S W).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ :
        Set (SLocalHomogeneousThetaQuotient F S ν ω))) :
    q ∈ closure (range (sLocalThetaPrincipalValues F S W)) := by
  let P := sLocalThetaPrincipalValues F S W
  let R := P.toLinearMap.range.topologicalClosure
  change q ∈ closure (P.toLinearMap.range : Set (E F S))
  rw [← Submodule.topologicalClosure_coe]
  change q ∈ R
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : T2Space (SIdeleQuotient F S) := inferInstance
  letI : PolynormableSpace ℂ (E F S) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  letI : IsClosed (R : Set (E F S)) := P.toLinearMap.range.isClosed_topologicalClosure
  letI : PolynormableSpace ℂ (E F S ⧸ R) := polynormableSpace_complex_quotient R
  by_contra hn
  have hne : R.mkQL q ≠ 0 := fun hz ↦ hn ((Submodule.Quotient.mk_eq_zero R).mp hz)
  obtain ⟨⟨p,hp⟩, hpq⟩ := (PolynormableSpace.withSeminorms ℂ (E F S ⧸ R)).separating_of_T1 _ hne
  obtain ⟨l,hl,_⟩ := seminorm_support p hp (R.mkQL q)
  let L := l.comp R.mkQL
  let u (k : K F S) := L (sLocalNormOneAction F S k q)
  have huc : Continuous u := L.continuous.comp
    ((continuous_sLocalThetaTranslate F S).comp (continuous_subtype_val.prodMk continuous_const))
  have hLp : MemLp u 2 ν := huc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hu : u =ᵐ[ν] 0 := by
    apply ae_eq_zero_of_character_integral_eq_zero ν hLp
    intro ω
    obtain ⟨s,_,_,_,_,hp⟩ := sLocalThetaComponent_pettisSection F S ν ω
    obtain ⟨y,hy⟩ := section_component_principal_mem_range F S ν W ω s hp q (hq ω)
    have hzero : R.mkQL (P y) = 0 :=
      (Submodule.Quotient.mk_eq_zero R).mpr
        (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ y))
    have h := (hp q L).2
    change L ((ν.real univ : ℂ) • s (sLocalThetaToComponent F S ν ω q)) =
      ∫ k, L ((((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q) ∂ν at h
    rw [← hy, map_smul] at h
    change (ν.real univ : ℂ) • l (R.mkQL (P y)) = _ at h
    rw [hzero, map_zero, smul_zero] at h
    refine (integral_congr_ae (.of_forall fun k ↦ ?_)).trans h.symm
    rw [map_smul, Circle.coe_inv_eq_conj]
    rfl
  have h1 := congrFun (Measure.eq_of_ae_eq hu huc continuous_const) 1
  change L (sLocalNormOneAction F S 1 q) = 0 at h1
  rw [map_one] at h1
  change l (R.mkQL q) = 0 at h1
  exact hpq (by simpa only [h1, norm_zero] using hl.symm)

private abbrev LocalUnits (v : S) := (v.val.adicCompletion F)ˣ

/-- Membership in the ordinary range closure is exactly membership in the
verified homogeneous ranges at every norm-one character. -/
theorem sLocalTheta_mem_closure_principalRange_iff_components
    [∀ v : S, MeasurableSpace (LocalUnits F S v)] [∀ v : S, BorelSpace (LocalUnits F S v)]
    (μ : ∀ v : S, Measure (LocalUnits F S v)) [∀ v : S, (μ v).IsHaarMeasure]
    [∀ v : S, SigmaFinite (μ v)]
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (hν : IsWeilQuotientMeasure (sUnitImage F S)
      (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
      Measure.count (sLocalClassHaar F S ν))
    (W : Finset S) (q : E F S) :
    q ∈ closure (range (sLocalThetaPrincipalValues F S W)) ↔
      ∀ ω, sLocalThetaToComponent F S ν ω q ∈
        ((sLocalFiniteNonzeroTestSubspace F S W).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ :
          Set (SLocalHomogeneousThetaQuotient F S ν ω)) := by
  refine ⟨fun hq ω ↦ ?_, sLocalTheta_mem_closure_principalRange_of_components F S ν W q⟩
  let C := sLocalThetaToComponent F S ν ω
  have hC := (sLocalFiniteNonzeroTestSubspace_map_isClosed F S μ ν hν ω W).preimage C.continuous
  apply (hC.closure_subset_iff.mpr ?_) hq
  rintro _ ⟨x,rfl⟩
  rw [← component_principal_range F S ν W ω]
  exact ⟨x,rfl⟩

/-- The ordinary range closure is cut out by the explicit pole bounds for
the continued local zeta integrals of a representative. -/
theorem sLocalTheta_mem_closure_principalRange_iff_poleBounds
    [∀ v : S, MeasurableSpace (LocalUnits F S v)] [∀ v : S, BorelSpace (LocalUnits F S v)]
    (μ : ∀ v : S, Measure (LocalUnits F S v)) [∀ v : S, (μ v).IsHaarMeasure]
    [∀ v : S, SigmaFinite (μ v)]
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (hν : IsWeilQuotientMeasure (sUnitImage F S)
      (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
      Measure.count (sLocalClassHaar F S ν))
    (W : Finset S) (f : Test F S) :
    (Submodule.Quotient.mk f : E F S) ∈ closure (range (sLocalThetaPrincipalValues F S W)) ↔
      ∀ (ω : PontryaginDual (K F S)) (c : ℂ),
        ((sLocalSelectedFinitePoleCount F S ω W c : ℤ) - (sLocalPoleCount F S ω c : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt (sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
            (sLocalComplexArchParameters F S ω) f) c := by
  rw [sLocalTheta_mem_closure_principalRange_iff_components F S ν μ hν W]
  apply forall_congr'
  intro ω
  exact sLocal_mk_mem_selected_finiteImage_iff_poleBound F S μ ν hν ω W f

/-- Where the characters are confined to a fixed finite set, the ordinary
principal-value range is closed in the ordinary quotient topology. -/
theorem sLocalTheta_principalRange_inter_finiteComponents_isClosed
    [∀ v : S, MeasurableSpace (LocalUnits F S v)] [∀ v : S, BorelSpace (LocalUnits F S v)]
    (μ : ∀ v : S, Measure (LocalUnits F S v)) [∀ v : S, (μ v).IsHaarMeasure]
    [∀ v : S, SigmaFinite (μ v)]
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (hν : IsWeilQuotientMeasure (sUnitImage F S)
      (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
      Measure.count (sLocalClassHaar F S ν))
    (W : Finset S) (A : Finset (PontryaginDual (K F S))) :
    IsClosed (range (sLocalThetaPrincipalValues F S W) ∩
      {q | ∀ ω ∉ A, sLocalThetaToComponent F S ν ω q = 0}) := by
  let R := range (sLocalThetaPrincipalValues F S W)
  let M : Set (E F S) := {q | ∀ ω ∉ A, sLocalThetaToComponent F S ν ω q = 0}
  have hM : IsClosed M := by
    have he : M = ⋂ ω : {ω : PontryaginDual (K F S) // ω ∉ A},
        (sLocalThetaToComponent F S ν ω.val).toLinearMap.ker := by
      ext q
      simp only [M, Set.mem_ofPred_eq, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker]
      exact ⟨fun h ω ↦ h ω.val ω.property, fun h ω hω ↦ h ⟨ω,hω⟩⟩
    rw [he]
    refine isClosed_iInter fun ω ↦ ?_
    obtain ⟨s, hs, _, _, _, _⟩ := sLocalThetaComponent_pettisSection F S ν ω.val
    letI : T2Space (E F S) := sLocalThetaQuotient_t2Space F S
    letI : T2Space (SLocalHomogeneousThetaQuotient F S ν ω.val) :=
      (hs.isEmbedding (sLocalThetaToComponent F S ν ω.val).continuous s.continuous).t2Space
    exact (sLocalThetaToComponent F S ν ω.val).isClosed_ker
  have he : R ∩ M = closure R ∩ M := by
    refine Set.Subset.antisymm (fun q hq ↦ ⟨subset_closure hq.1,hq.2⟩) ?_
    rintro q ⟨hq,hm⟩
    refine ⟨sLocalTheta_mem_principalRange_of_finite_components F S ν W q A hm ?_,hm⟩
    have hc := (sLocalTheta_mem_closure_principalRange_iff_components F S ν μ hν W q).mp hq
    exact fun ω _ ↦ hc ω
  change IsClosed (R ∩ M)
  rw [he]
  exact isClosed_closure.inter hM

end
end Masullo
