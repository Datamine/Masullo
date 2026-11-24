import GlobalThetaDualGeneration
import AdelicSchwartzNuclear
import StrictQuotientStages

open Bornology Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

universe u

section Quotient

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (M : Submodule ℂ E)

omit [ContinuousSMul ℂ E] in
theorem homogeneousSection_complete {Q : Type u} [AddCommGroup Q] [Module ℂ Q]
    [TopologicalSpace Q] [IsTopologicalAddGroup Q] [T2Space E]
    (h : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (p : E →L[ℂ] Q) (j : Q →L[ℂ] E) (hj : LeftInverse p j) :
    @CompleteSpace Q (IsTopologicalAddGroup.rightUniformSpace Q) := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace E := h
  have hr : range j = {x : E | j (p x) = x} := by
    ext x
    change (∃ q, j q = x) ↔ j (p x) = x
    exact ⟨by rintro ⟨q, rfl⟩; rw [hj q], fun hx ↦ ⟨p x, hx⟩⟩
  have hclosed : IsClosed (range j) := hr ▸ isClosed_eq (j.continuous.comp p.continuous) continuous_id
  exact (AddMonoidHom.isUniformInducing_of_isInducing
    (f := j.toLinearMap.toAddMonoidHom) (hj.isEmbedding p.continuous j.continuous).isInducing
    ).completeSpace hclosed.isComplete

omit [ContinuousSMul ℂ E] in
private theorem homogeneousQuotient_montel
    (h : @CompleteSpace (E ⧸ M) (IsTopologicalAddGroup.rightUniformSpace (E ⧸ M)))
    (hN : NuclearLocallyConvex.{u, u} (E ⧸ M)) : MontelSpace ℂ (E ⧸ M) := by
  letI : UniformSpace (E ⧸ M) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E ⧸ M) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (E ⧸ M) := h
  letI : PolynormableSpace ℂ (E ⧸ M) := hN.2.1
  exact ⟨fun _ hclosed hbounded ↦
    (nuclearLocallyConvex_totallyBounded hN hbounded).isCompact_of_isClosed hclosed⟩

omit [IsTopologicalAddGroup E] in
private theorem homogeneousQuotient_dualStructure
    (hN : NuclearLocallyConvex.{u, u} (StrongDual ℂ E))
    (hC : CompleteSpace (StrongDual ℂ E))
    (hEmb : IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) :
    let D := StrongDual ℂ (E ⧸ M)
    NuclearLocallyConvex.{u, u} D ∧ CompleteSpace D ∧ MontelSpace ℂ D := by
  letI : CompleteSpace (StrongDual ℂ E) := hC
  let P : StrongDual ℂ (E ⧸ M) →L[ℂ] StrongDual ℂ E :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL
  have hclosed : IsClosed (range P) := by
    rw [quotientDual_strongRange M]
    rw [show {l : StrongDual ℂ E | ∀ x ∈ M, l x = 0} =
      ⋂ x : M, {l : StrongDual ℂ E | l x.val = 0} from by ext l; simp]
    exact isClosed_iInter fun x ↦ isClosed_eq (continuous_eval_const x.val) continuous_const
  have hN' := nuclearLocallyConvex_of_embedding P hEmb hN
  have hC' := (AddMonoidHom.isUniformInducing_of_isInducing
    (f := P.toLinearMap.toAddMonoidHom) hEmb.isInducing).completeSpace hclosed.isComplete
  refine ⟨hN', hC', ?_⟩
  letI := hC'
  exact ⟨fun _ hclosed hbounded ↦
    (nuclearLocallyConvex_totallyBounded hN' hbounded).isCompact_of_isClosed hclosed⟩

end Quotient

/-- A strict locally convex presentation by nuclear Fréchet spaces. -/
def HasStrictNuclearFrechetPresentation (Q : Type u)
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] : Prop :=
  ∃ (V : ℕ → Type u) (_ : ∀ n, AddCommGroup (V n)) (_ : ∀ n, Module ℂ (V n))
    (_ : ∀ n, TopologicalSpace (V n)) (D : LinearInductivePresentation Q V),
    (∀ n, IsFrechetTVS (V n) ∧ NuclearLocallyConvex.{u, u} (V n)) ∧
    (∀ n, IsClosedEmbedding (D.incl n)) ∧
    (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
    (∀ r : Seminorm ℂ Q, (∀ n, Continuous (r.comp (D.incl n).toLinearMap)) → Continuous r)

theorem HasStrictNuclearFrechetPresentation.barrelled {Q : Type u}
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (hQ : HasStrictNuclearFrechetPresentation Q) : BarrelledSpace ℂ Q := by
  obtain ⟨V, a, m, t, D, hF, _, _, hFinal⟩ := hQ
  exact barrelled_of_frechet_final D.incl (fun n ↦ (hF n).1) hFinal

private theorem homogeneousStrongDual_barrelled {Q : Type u}
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    (hF : HasStrictNuclearFrechetPresentation Q)
    (hN : NuclearLocallyConvex.{u, u} Q)
    (hC : @CompleteSpace Q (IsTopologicalAddGroup.rightUniformSpace Q)) :
    BarrelledSpace ℂ (StrongDual ℂ Q) := by
  letI : T2Space Q := hN.1
  letI : PolynormableSpace ℂ Q := hN.2.1
  letI : ContinuousSMul ℂ Q := (PolynormableSpace.withSeminorms ℂ Q).continuousSMul
  letI : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  letI : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Q := hC
  letI : BarrelledSpace ℂ Q := hF.barrelled
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear hN
  apply strongDual_barrelled_of_bidually_surjective
  intro ℓ
  obtain ⟨x, hx⟩ := e.surjective ℓ
  exact ⟨x, ContinuousLinearMap.ext fun L ↦ (he x L).symm.trans (DFunLike.congr_fun hx L)⟩

/-- A continuous linear retract inherits a strict nuclear Fréchet presentation.
The stages are the intersections with the range of the continuous projection. -/
theorem HasStrictNuclearFrechetPresentation.of_retract {E Q : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    (hE : HasStrictNuclearFrechetPresentation E)
    (p : E →L[ℂ] Q) (j : Q →L[ℂ] E) (hj : LeftInverse p j) :
    HasStrictNuclearFrechetPresentation Q := by
  obtain ⟨W, a, m, t, D, hF, hIn, _, hFinal⟩ := hE
  let P := j.comp p
  let M := (ContinuousLinearMap.id ℂ E - P).ker
  have hM (x : E) : x ∈ M ↔ P x = x := by
    change x - P x = 0 ↔ P x = x
    rw [sub_eq_zero, eq_comm]
  let V (n : ℕ) := M.comap (D.incl n).toLinearMap
  have hV (n : ℕ) : IsClosed (V n : Set (W n)) := by
    change IsClosed ((D.incl n) ⁻¹' (M : Set E))
    exact (ContinuousLinearMap.id ℂ E - P).isClosed_ker.preimage (D.incl n).continuous
  have hFr (n : ℕ) := isFrechetTVS_closedSubmodule (hF n).1 (V n) (hV n)
  let phi (n : ℕ) : V n →L[ℂ] Q := p.comp ((D.incl n).comp (V n).subtypeL)
  have hphi (n : ℕ) (x : V n) : j (phi n x) = D.incl n x.val :=
    (hM _).mp x.property
  have hEmb : IsEmbedding j := hj.isEmbedding p.continuous j.continuous
  letI : T2Space Q := hEmb.t2Space
  have hI (n : ℕ) : IsClosedEmbedding (phi n) := by
    apply (hFr n).isClosedEmbedding
    apply hEmb.of_comp_iff.mp
    rw [show j ∘ phi n = D.incl n ∘ Subtype.val from funext (hphi n)]
    exact (hIn n).isEmbedding.comp IsEmbedding.subtypeVal
  have hQ (r : Seminorm ℂ Q) (hr : ∀ n, Continuous (r.comp (phi n).toLinearMap)) :
      Continuous r := by
    have hp : Continuous (r.comp p.toLinearMap) := by
      apply hFinal
      intro n
      obtain ⟨m, f, hf⟩ := frechet_factorization_of_isFrechetTVS (hF n).1
        (fun k ↦ (hF k).1) (P.comp (D.incl n)) D.incl D.injective_incl D.exhaust
      have hfx (x : W n) : D.incl m (f x) = P (D.incl n x) := DFunLike.congr_fun hf x
      let f' : W n →L[ℂ] V m := f.codRestrict _ fun x ↦ by
        change D.incl m (f x) ∈ M
        rw [hfx, hM]
        change j (p (j (p (D.incl n x)))) = j (p (D.incl n x))
        rw [hj]
      have he : (r.comp p.toLinearMap).comp (D.incl n).toLinearMap =
          (r.comp (phi m).toLinearMap).comp f'.toLinearMap := by
        ext x
        change r (p (D.incl n x)) = r (p (D.incl m (f x)))
        rw [hfx, show p (P (D.incl n x)) = p (D.incl n x) from hj _]
      rw [he]
      exact (hr m).comp f'.continuous
    exact (hp.comp j.continuous).congr fun x ↦ by
      change r (p (j x)) = r x
      rw [hj]
  let A : LinearInductivePresentation Q (fun n ↦ V n) :=
    { incl := phi
      transition := fun {s t} h ↦ ((D.transition h).comp (V s).subtypeL).codRestrict _ fun x ↦ by
        change D.incl t (D.transition h x.val) ∈ M
        rw [D.incl_transition]
        exact x.property
      injective_incl := fun n ↦ (hI n).isEmbedding.injective
      incl_transition := fun {s t} h x ↦ by
        change p (D.incl t (D.transition h x.val)) = p (D.incl s x.val)
        rw [D.incl_transition]
      exhaust := fun q ↦ by
        obtain ⟨n, x, hx⟩ := D.exhaust (j q)
        have hx' : x ∈ V n := by
          change D.incl n x ∈ M
          rw [hx, hM]
          exact congrArg j (hj q)
        exact ⟨n, ⟨x, hx'⟩, (congrArg p hx).trans (hj q)⟩
      continuous_limit := fun L ↦ ⟨fun h n ↦ h.comp (phi n).continuous, fun h ↦ by
        apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L
        intro i
        apply hQ
        intro n
        exact ((norm_withSeminorms ℂ ℂ).continuous_seminorm i).comp (h n)⟩ }
  refine ⟨fun n ↦ V n, inferInstance, inferInstance, inferInstance, A,
    fun n ↦ ⟨hFr n, nuclearLocallyConvex_submodule (hF n).2 (V n)⟩, hI, ?_, hQ⟩
  intro n
  apply (hI (n+1)).of_comp_iff.mp
  have he : A.incl (n+1) ∘ A.transition (Nat.le_succ n) = A.incl n :=
    funext (A.incl_transition (Nat.le_succ n))
  rw [he]
  exact hI n

section Global

variable (F : Type u) [Field F] [NumberField F]

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (μ : Measure (Idele F)) [μ.IsHaarMeasure] (ω : PontryaginDual (normOneIdeleClass F))

private abbrev GlobalComponentKernel := globalIdelicZetaComponentKernel F μ ω

private theorem globalComponentKernel_closed :
    IsClosed (GlobalComponentKernel F μ ω : Set (GlobalBruhat F)) := by
  rw [show (GlobalComponentKernel F μ ω : Set (GlobalBruhat F)) =
    ⋂ y : ℝ, {f | globalThetaLineTestEval F μ ω y f = 0} from by
      ext f
      simp only [GlobalComponentKernel, globalIdelicZetaComponentKernel, Submodule.mem_iInf,
        SetLike.mem_coe, LinearMap.mem_ker, mem_iInter, mem_ofPred_eq]
      rfl]
  exact isClosed_iInter fun y ↦ isClosed_eq (globalThetaLineTestEval F μ ω y).continuous continuous_const

/-- The global homogeneous theta quotient is complete, nuclear and Montel. -/
theorem globalHomogeneousTheta_primalStructure :
    let Q := GlobalBruhat F ⧸ GlobalComponentKernel F μ ω
    NuclearLocallyConvex.{u, u} Q ∧
      @CompleteSpace Q (IsTopologicalAddGroup.rightUniformSpace Q) ∧ MontelSpace ℂ Q := by
  let M := GlobalComponentKernel F μ ω
  have hM := globalComponentKernel_closed F μ ω
  have hN := nuclearLocallyConvex_quotient (globalBruhat_nuclear F) M hM
  letI : T2Space (GlobalThetaQuotient F) := globalThetaQuotient_t2Space F
  obtain ⟨j, hj⟩ := globalThetaComponent_section F μ ω
  have hC := homogeneousSection_complete (globalThetaQuotient_complete F)
    (globalThetaToComponent F μ ω) j hj
  exact ⟨hN, hC, homogeneousQuotient_montel M hC hN⟩

/-- The strong dual of the global homogeneous theta quotient is complete, nuclear and Montel. -/
theorem globalHomogeneousTheta_dualStructure :
    let D := StrongDual ℂ (GlobalBruhat F ⧸ GlobalComponentKernel F μ ω)
    NuclearLocallyConvex.{u, u} D ∧ CompleteSpace D ∧ MontelSpace ℂ D :=
  homogeneousQuotient_dualStructure (GlobalComponentKernel F μ ω)
    (globalBruhat_strongDual_nuclear F) (globalBruhat_strongDual_complete F)
    (globalHomogeneousThetaTranspose_isEmbedding F μ ω)

/-- The global homogeneous quotient has a strict nuclear Fréchet presentation. -/
theorem globalHomogeneousTheta_frechetPresentation :
    HasStrictNuclearFrechetPresentation (GlobalBruhat F ⧸ GlobalComponentKernel F μ ω) := by
  letI : T2Space (GlobalThetaQuotient F) := globalThetaQuotient_t2Space F
  obtain ⟨j, hj⟩ := globalThetaComponent_section F μ ω
  apply HasStrictNuclearFrechetPresentation.of_retract _
    (globalThetaToComponent F μ ω) j hj
  obtain ⟨W, D, hF, hI, hT, hFinal, hN, _⟩ := globalTheta_exists_strictFrechet F
  exact ⟨fun n ↦ ↥(W n), inferInstance, inferInstance, inferInstance, D,
    fun n ↦ ⟨hF n, hN (archimedeanSchwartz_nuclear F) n⟩, hI, hT, hFinal⟩

/-- Both the global homogeneous quotient and its strong dual are barrelled. -/
theorem globalHomogeneousTheta_barrelled :
    let Q := GlobalBruhat F ⧸ GlobalComponentKernel F μ ω
    BarrelledSpace ℂ Q ∧ BarrelledSpace ℂ (StrongDual ℂ Q) := by
  have hF := globalHomogeneousTheta_frechetPresentation F μ ω
  obtain ⟨hN, hC, _⟩ := globalHomogeneousTheta_primalStructure F μ ω
  exact ⟨hF.barrelled, homogeneousStrongDual_barrelled hF hN hC⟩

end Global

section SLocal

variable (F : Type u) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev X := sLocalBruhatImage F S
private abbrev Θ := SLocalThetaQuotient F S
private abbrev N := (sLocalThetaOperator F S).ker

local instance : MeasurableSpace (SIdeleQuotient F S) := borel _
local instance : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩

variable (ν : Measure (K F S)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F S))

private abbrev M := sLocalHomogeneousThetaKernel F S ν ω

private abbrev sLocalLine (y : ℝ) : ℂ := 1 + (y : ℂ) * Complex.I

private def sLocalMellinTest (τ : PontryaginDual (K F S)) (y : ℝ) : StrongDual ℂ (X F S) :=
  sLocalThetaZetaCLM F S ν τ (sLocalLine y) (by simp)

private theorem sLocalMellinKernel (f : X F S) :
    f ∈ N F S ↔ ∀ (τ : PontryaginDual (K F S)) y, sLocalMellinTest F S ν τ y f = 0 := by
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI := sLocalIdeles_secondCountable F S
  letI : SecondCountableTopology (SIdeleQuotient F S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : SecondCountableTopology (K F S) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : TopologicalSpace.PseudoMetrizableSpace (K F S) := inferInstance
  letI := sLocalThetaNormOne_compact F S
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  change sLocalThetaOperator F S f = 0 ↔ _
  exact sLocalTheta_zero_iff_verticalZeta F S ν f 1 zero_lt_one

private theorem sLocalMellinComponentKernel (f : X F S) :
    f ∈ M F S ν ω ↔ ∀ y, sLocalMellinTest F S ν ω y f = 0 := by
  simp only [M, sLocalHomogeneousThetaKernel, Submodule.mem_iInf, LinearMap.mem_ker, sLocalMellinTest]
  rfl

private def sLocalMellinEval (τ : PontryaginDual (K F S)) (y : ℝ) : StrongDual ℂ (Θ F S) :=
  (N F S).liftQL (sLocalMellinTest F S ν τ y) (fun f hf ↦
    (sLocalMellinKernel F S ν f).mp hf τ y)

private theorem sLocalMellin_separates (q : Θ F S)
    (hq : ∀ (τ : PontryaginDual (K F S)) y, sLocalMellinEval F S ν τ y q = 0) : q = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((sLocalMellinKernel F S ν f).mpr hq)

/-- The norm-one S-idele class action on ordinary S-local theta. -/
def sLocalNormOneAction : K F S →* (Θ F S →L[ℂ] Θ F S) where
  toFun k := sLocalThetaTranslate F S k.val
  map_one' := ContinuousLinearMap.ext (sLocalThetaTranslate_one F S)
  map_mul' u v := ContinuousLinearMap.ext (sLocalThetaTranslate_mul F S u.val v.val)

/-- The relations for the prescribed compact character in the ordinary quotient. -/
def sLocalTwistedDifferences (τ : PontryaginDual (K F S)) : Submodule ℂ (Θ F S) :=
  Submodule.span ℂ (range fun z : K F S × Θ F S ↦
    z.2 - (((τ.toMonoidHom z.1)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S z.1 z.2)

private theorem sLocalMellinEval_translate (τ : PontryaginDual (K F S)) (y : ℝ) (k : K F S) (q : Θ F S) :
    sLocalMellinEval F S ν τ y (sLocalNormOneAction F S k q) =
      (τ k : ℂ) * sLocalMellinEval F S ν τ y q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective k.val
  change sLocalMellinEval F S ν τ y (sLocalThetaTranslate F S k.val (Submodule.Quotient.mk f)) = _
  rw [← hg, show sLocalThetaTranslate F S (QuotientGroup.mk g) = sLocalThetaTranslateIdeles F S g from rfl,
    sLocalThetaTranslateIdeles_mk]
  let z := sLocalLine y
  have hz : 0 < z.re := by simp [z]
  change sLocalThetaZetaIntegral F S ν τ (sLocalBruhatLeftTranslate F S g f) z =
    (τ k : ℂ) * sLocalThetaZetaIntegral F S ν τ f z
  rw [(sLocalThetaZeta_integrable_eq_radial F S ν τ _ z hz).2,
    (sLocalThetaZeta_integrable_eq_radial F S ν τ f z hz).2, sLocalRadialMellin, sLocalRadialMellin,
    ← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  let q : SIdeleQuotient F S := QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))
  change Complex.exp (z * (t : ℂ)) *
    sLocalHomogeneousTheta F S ν τ (sLocalBruhatLeftTranslate F S g f).val q =
      (τ k : ℂ) * (Complex.exp (z * (t : ℂ)) * sLocalHomogeneousTheta F S ν τ f.val q)
  rw [sLocalHomogeneousTheta_leftTranslate_normOne F S ν τ k g hg f, mul_left_comm (Complex.exp _)]

set_option maxHeartbeats 2200000 in
private theorem sLocalIsotypeProjection :
    ∃ P : Θ F S →L[ℂ] Θ F S,
      (∀ q k, sLocalNormOneAction F S k (P q) = (ω k : ℂ) • P q) ∧
      (∀ q, (∀ k, sLocalNormOneAction F S k q = (ω k : ℂ) • q) → P q = q) ∧
      (∀ q, P q = 0 ↔
        q ∈ (sLocalTwistedDifferences F S ω).topologicalClosure) ∧
      (∀ (τ : PontryaginDual (K F S)) y q,
        sLocalMellinEval F S ν τ y (P q) =
          if ω = τ then sLocalMellinEval F S ν τ y q else 0) ∧
      ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q)
        ((ν.real univ : ℂ) • P q) := by
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  letI : UniformSpace (Θ F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Θ F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Θ F S) := sLocalThetaQuotient_complete F S
  letI : T2Space (Θ F S) := sLocalThetaQuotient_t2Space F S
  letI : PolynormableSpace ℂ (Θ F S) := polynormableSpace_complex_quotient (N F S)
  letI : Module ℝ (Θ F S) := Module.restrictScalars ℝ ℂ (Θ F S)
  letI : IsScalarTower ℝ ℂ (Θ F S) := IsScalarTower.restrictScalars ℝ ℂ (Θ F S)
  letI : LocallyConvexSpace ℝ (Θ F S) :=
    (PolynormableSpace.withSeminorms ℂ (Θ F S)).toLocallyConvexSpace
  have hρ : Continuous (fun z : K F S × Θ F S ↦ sLocalNormOneAction F S z.1 z.2) :=
    (continuous_sLocalThetaTranslate F S).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hfixed, P, hP, hRange, _, hProj, _, hKer⟩ := compactGroupIsotypicAverage (sLocalNormOneAction F S) hρ
    ω.toMonoidHom (map_continuous ω) ν
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    have hp := Measure.measure_pos_of_nonempty_interior (s := (univ : Set (K F S))) ν (by simp)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)).ne'
  refine ⟨(ν.real univ : ℂ)⁻¹ • P, ?_, ?_, ?_, (fun τ y q ↦ ?_), ?_⟩
  · intro q k
    have hmem : P q ∈ range P := mem_range_self q
    rw [hRange] at hmem
    have h := (hfixed (P q)).mp hmem k
    change sLocalNormOneAction F S k ((ν.real univ : ℂ)⁻¹ • P q) =
      (ω k : ℂ) • ((ν.real univ : ℂ)⁻¹ • P q)
    rw [map_smul, h, smul_comm]
    rfl
  · let A := (ν.real univ : ℂ)⁻¹ • P
    intro q he
    have hq : q ∈ range P := by rw [hRange]; exact (hfixed q).mpr he
    obtain ⟨x, rfl⟩ := hq
    have hx : A (A x) = A x := hProj x
    change A ((ν.real univ : ℂ)⁻¹ • P x) = (ν.real univ : ℂ)⁻¹ • P x at hx
    rw [map_smul] at hx
    exact (smul_right_injective _ (inv_ne_zero hmass)) hx
  · intro q
    change (ν.real univ : ℂ)⁻¹ • P q = 0 ↔ q ∈ (sLocalTwistedDifferences F S ω).topologicalClosure
    have hk : P.ker = (sLocalTwistedDifferences F S ω).topologicalClosure := by
      simpa only [sLocalTwistedDifferences, actionDifferenceSpan, twistedCircleAction,
        MonoidHom.coe_mk, OneHom.coe_mk, Circle.smul_def, smul_apply] using hKer
    rw [smul_eq_zero, or_iff_right (inv_ne_zero hmass), ← hk]
    rfl
  · let L := sLocalMellinEval F S ν τ y
    have h := (hP q L).2
    change L (P q) = ∫ k, L ((((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q) ∂ν at h
    have hval (k : K F S) :
        L ((((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q) =
          (star (ω k : ℂ) * (τ k : ℂ)) * L q := by
      rw [map_smul, Circle.coe_inv_eq_conj, smul_eq_mul, mul_assoc, sLocalMellinEval_translate F S ν τ y]
      rfl
    rw [integral_congr_ae (.of_forall hval), integral_mul_const, integral_character_pair ν ω τ] at h
    change L ((ν.real univ : ℂ)⁻¹ • P q) = if ω = τ then L q else 0
    rw [map_smul, smul_eq_mul, h]
    split_ifs <;> simp [hmass]

  · intro q
    change HasPositivePettisIntegral ν _ ((ν.real univ : ℂ) • ((ν.real univ : ℂ)⁻¹ • P q))
    rw [smul_smul, mul_inv_cancel₀ hmass, one_smul]
    exact hP q

/-- The S-local map from ordinary theta classes to the character quotient. -/
def sLocalThetaToComponent : Θ F S →L[ℂ] SLocalHomogeneousThetaQuotient F S ν ω :=
  (N F S).liftQL (M F S ν ω).mkQL fun f hf ↦ (Submodule.Quotient.mk_eq_zero _).mpr <|
    (sLocalMellinComponentKernel F S ν ω f).mpr ((sLocalMellinKernel F S ν f).mp hf ω)

/-- The product of the S-local homogeneous quotient maps. -/
def sLocalThetaToAllComponents :
    Θ F S →L[ℂ] (∀ τ : PontryaginDual (K F S), SLocalHomogeneousThetaQuotient F S ν τ) :=
  ContinuousLinearMap.pi (sLocalThetaToComponent F S ν)

theorem sLocalThetaToAllComponents_injective : Injective (sLocalThetaToAllComponents F S ν) := by
  intro q r h
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) r
  apply (Submodule.Quotient.eq (N F S)).mpr
  apply (sLocalMellinKernel F S ν (f - g)).mpr
  intro τ
  have hτ :
      (Submodule.Quotient.mk f : SLocalHomogeneousThetaQuotient F S ν τ) = Submodule.Quotient.mk g :=
    congrFun h τ
  exact (sLocalMellinComponentKernel F S ν τ (f - g)).mp ((Submodule.Quotient.eq _).mp hτ)

/-- The ordinary-to-homogeneous S-local theta map is open. -/
theorem sLocalThetaToComponent_isOpenMap : IsOpenMap (sLocalThetaToComponent F S ν ω) :=
  IsOpenMap.of_comp (N F S).mkQL.continuous (Submodule.Quotient.mk_surjective (N F S))
    (M F S ν ω).isOpenQuotientMap_mkQL.isOpenMap

/-- Haar averages on ordinary theta factor through the S-local homogeneous quotient. -/
theorem sLocalThetaComponent_pettisSection :
    ∃ s : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] Θ F S,
      LeftInverse (sLocalThetaToComponent F S ν ω) s ∧
      (∀ q k, sLocalNormOneAction F S k (s q) = (ω k : ℂ) • s q) ∧
      (sLocalThetaToComponent F S ν ω).ker =
        (sLocalTwistedDifferences F S ω).topologicalClosure ∧
      (∀ q, (∀ k, sLocalNormOneAction F S k q = (ω k : ℂ) • q) →
        s (sLocalThetaToComponent F S ν ω q) = q) ∧
      ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q)
        ((ν.real univ : ℂ) • s (sLocalThetaToComponent F S ν ω q)) := by
  obtain ⟨P, hEig, hFix, hKer, hP, hPettis⟩ := sLocalIsotypeProjection F S ν ω
  let A := P.comp (N F S).mkQL
  have hA : M F S ν ω ≤ A.ker := by
    intro f hf
    apply sLocalMellin_separates F S ν (A f)
    intro τ y
    change sLocalMellinEval F S ν τ y (P ((N F S).mkQL f)) = 0
    rw [hP]
    split_ifs with he
    · subst τ
      exact (sLocalMellinComponentKernel F S ν ω f).mp hf y
    · rfl
  let s := (M F S ν ω).liftQL A hA
  have hs : LeftInverse (sLocalThetaToComponent F S ν ω) s := by
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (M F S ν ω) q
    obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective (N F S) (A f)
    change sLocalThetaToComponent F S ν ω (A f) = Submodule.Quotient.mk f
    rw [← hg]
    change (Submodule.Quotient.mk g : SLocalHomogeneousThetaQuotient F S ν ω) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    apply (sLocalMellinComponentKernel F S ν ω (g - f)).mpr
    intro y
    have he := congrArg (sLocalMellinEval F S ν ω y) hg
    change sLocalMellinTest F S ν ω y g = sLocalMellinEval F S ν ω y (P ((N F S).mkQL f)) at he
    rw [hP, ite_eq_left rfl] at he
    rw [map_sub, sub_eq_zero]
    exact he
  refine ⟨s, hs, ?_, ?_, ?_, ?_⟩
  · intro q k
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (M F S ν ω) q
    exact hEig ((N F S).mkQL f) k
  · ext q
    change sLocalThetaToComponent F S ν ω q = 0 ↔ _
    rw [← hKer]
    have he : P q = s (sLocalThetaToComponent F S ν ω q) := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
      rfl
    rw [he, ← map_zero s]
    exact hs.injective.eq_iff.symm

  · intro q hq
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
    exact hFix ((N F S).mkQL f) hq
  · intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
    exact hPettis ((N F S).mkQL f)

set_option maxHeartbeats 1500000 in
/-- The unnormalized S-local Pettis map is an open surjection onto the closed
character subspace, induced by a topological isomorphism from the actual quotient. -/
theorem sLocalThetaComponent_pettisEquiv :
    ∃ e : SLocalHomogeneousThetaQuotient F S ν ω ≃L[ℂ]
        thetaCharacterSubspace (sLocalNormOneAction F S) (fun k ↦ (ω k : ℂ)),
      IsOpenMap (e ∘ sLocalThetaToComponent F S ν ω) ∧
      Surjective (e ∘ sLocalThetaToComponent F S ν ω) ∧
      ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q)
        ↑(e (sLocalThetaToComponent F S ν ω q)) := by
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  letI : T2Space (Θ F S) := sLocalThetaQuotient_t2Space F S
  obtain ⟨s, hs, hEig, _, hFix, hPettis⟩ := sLocalThetaComponent_pettisSection F S ν ω
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    have hp := Measure.measure_pos_of_nonempty_interior (s := (univ : Set (K F S))) ν (by simp)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)).ne'
  let e := ContinuousLinearMap.equivThetaCharacterSubspace (sLocalNormOneAction F S)
    (fun k ↦ (ω k : ℂ)) _ s hs hEig hFix (Units.mk0 _ hmass)
  exact ⟨e, e.isOpenMap.comp (sLocalThetaToComponent_isOpenMap F S ν ω),
    e.surjective.comp hs.surjective, hPettis⟩

/-- The S-local isotypic section and the closed span defining its quotient. -/
theorem sLocalThetaComponent_isotypicSection :
    ∃ s : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] Θ F S,
      LeftInverse (sLocalThetaToComponent F S ν ω) s ∧
      (∀ q k, sLocalNormOneAction F S k (s q) = (ω k : ℂ) • s q) ∧
      (sLocalThetaToComponent F S ν ω).ker =
        (sLocalTwistedDifferences F S ω).topologicalClosure := by
  obtain ⟨s, hs, hEig, hKer, _, _⟩ := sLocalThetaComponent_pettisSection F S ν ω
  exact ⟨s, hs, hEig, hKer⟩

/-- Haar averaging splits the actual S-local homogeneous quotient map continuously. -/
theorem sLocalThetaComponent_section :
    ∃ s : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] Θ F S,
      LeftInverse (sLocalThetaToComponent F S ν ω) s := by
  obtain ⟨s, hs, _⟩ := sLocalThetaComponent_isotypicSection F S ν ω
  exact ⟨s, hs⟩

/-- The S-local homogeneous transpose embeds the topology of bounded convergence. -/
theorem sLocalHomogeneousThetaTranspose_isEmbedding :
    IsEmbedding (sLocalHomogeneousThetaTranspose F S ν ω) := by
  apply quotientDual_strongEmbedding_of_bounded_lifts
  intro B hB
  obtain ⟨j, hj⟩ := sLocalThetaComponent_section F S ν ω
  obtain ⟨C, hC, hCB⟩ := sLocalTheta_bounded_lift F S (j '' B) (hB.image j)
  refine ⟨C, hC.isVonNBounded ℂ, ?_⟩
  intro q hq
  obtain ⟨f, hf, he⟩ := hCB (mem_image_of_mem j hq)
  exact ⟨f, hf, (congrArg (sLocalThetaToComponent F S ν ω) he).trans (hj q)⟩

private theorem sLocalHomogeneousThetaKernel_closed :
    IsClosed (sLocalHomogeneousThetaKernel F S ν ω : Set (X F S)) := by
  rw [show (sLocalHomogeneousThetaKernel F S ν ω : Set (X F S)) =
    ⋂ y : ℝ, {f | sLocalThetaZetaCLM F S ν ω ((1 : ℂ) + (y : ℂ) * Complex.I) (by simp) f = 0}
    from by
      ext f
      simp [sLocalHomogeneousThetaKernel, LinearMap.mem_ker]]
  exact isClosed_iInter fun y ↦ isClosed_eq (sLocalThetaZetaCLM F S ν ω _ (by simp)).continuous
    continuous_const

/-- The actual S-local homogeneous theta quotient is complete, nuclear and Montel. -/
theorem sLocalHomogeneousTheta_primalStructure :
    let Q := SLocalHomogeneousThetaQuotient F S ν ω
    NuclearLocallyConvex.{u, u} Q ∧
      @CompleteSpace Q (IsTopologicalAddGroup.rightUniformSpace Q) ∧ MontelSpace ℂ Q := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  have hM := sLocalHomogeneousThetaKernel_closed F S ν ω
  have hN := nuclearLocallyConvex_quotient (sLocalBruhat_nuclear F S) M hM
  letI : T2Space (Θ F S) := sLocalThetaQuotient_t2Space F S
  obtain ⟨j, hj⟩ := sLocalThetaComponent_section F S ν ω
  have hC := homogeneousSection_complete (sLocalThetaQuotient_complete F S)
    (sLocalThetaToComponent F S ν ω) j hj
  exact ⟨hN, hC, homogeneousQuotient_montel M hC hN⟩

/-- The strong dual of the S-local homogeneous quotient is complete, nuclear and Montel. -/
theorem sLocalHomogeneousTheta_dualStructure :
    let D := StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω)
    NuclearLocallyConvex.{u, u} D ∧ CompleteSpace D ∧ MontelSpace ℂ D :=
  homogeneousQuotient_dualStructure (M F S ν ω)
    (sLocalBruhat_strongDual_nuclear F S) (sLocalBruhat_strongDual_complete F S)
    (sLocalHomogeneousThetaTranspose_isEmbedding F S ν ω)

/-- The S-local homogeneous quotient has a strict nuclear Fréchet presentation. -/
theorem sLocalHomogeneousTheta_frechetPresentation :
    HasStrictNuclearFrechetPresentation (SLocalHomogeneousThetaQuotient F S ν ω) := by
  letI : T2Space (Θ F S) := sLocalThetaQuotient_t2Space F S
  obtain ⟨j, hj⟩ := sLocalThetaComponent_section F S ν ω
  apply HasStrictNuclearFrechetPresentation.of_retract _ (sLocalThetaToComponent F S ν ω) j hj
  obtain ⟨W, D, hF, hI, hT, hFinal, hN, _⟩ := sLocalTheta_exists_strictFrechet F S
  exact ⟨fun n ↦ ↥(W n), inferInstance, inferInstance, inferInstance, D,
    fun n ↦ ⟨hF n, hN (archimedeanSchwartz_nuclear F) n⟩, hI, hT, hFinal⟩

/-- An integral-unit level in the kernel of the isotype makes the entire
homogeneous quotient Fréchet. -/
theorem sLocalHomogeneousTheta_isFrechet_of_unitLevel
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hn : ∀ (w : S) (a : H w), ‖a.val.val‖ = 1)
    (hω : ∀ a : ∀ w : S, H w, ∃ k : K F S,
      k.val = QuotientGroup.mk (angularLocalIdele F S H a) ∧ ω k = 1) :
    IsFrechetTVS (SLocalHomogeneousThetaQuotient F S ν ω) := by
  let W := sLocalThetaInvariantTestSpan F S H
  obtain ⟨s, hs, hEig, _⟩ := sLocalThetaComponent_isotypicSection F S ν ω
  have hi (q) : s q ∈ W := by
    apply mem_sLocalThetaInvariantTestSpan_of_fixed F S H hH hn
    intro a
    obtain ⟨k, hk, hχ⟩ := hω a
    have he := hEig q k
    change sLocalThetaTranslate F S k.val (s q) = (ω k : ℂ) • s q at he
    rw [hk, hχ, Circle.coe_one, one_smul] at he
    exact he
  let j := s.codRestrict W hi
  let p := (sLocalThetaToComponent F S ν ω).comp W.subtypeL
  have hp : LeftInverse p j := hs
  have he := hp.isEmbedding p.continuous j.continuous
  obtain ⟨_, hpoly, _, _⟩ := sLocalThetaInvariantTestSpan_isFrechet F S H hH hn
  exact ⟨inferInstance, (he.isInducing.withSeminorms (f := j.toLinearMap)
    (PolynormableSpace.withSeminorms ℂ W)).toPolynormableSpace,
    he.metrizableSpace, (sLocalHomogeneousTheta_primalStructure F S ν ω).2.1⟩

/-- Both the S-local homogeneous quotient and its strong dual are barrelled. -/
theorem sLocalHomogeneousTheta_barrelled :
    let Q := SLocalHomogeneousThetaQuotient F S ν ω
    BarrelledSpace ℂ Q ∧ BarrelledSpace ℂ (StrongDual ℂ Q) := by
  have hF := sLocalHomogeneousTheta_frechetPresentation F S ν ω
  obtain ⟨hN, hC, _⟩ := sLocalHomogeneousTheta_primalStructure F S ν ω
  exact ⟨hF.barrelled, homogeneousStrongDual_barrelled hF hN hC⟩

end SLocal

end
end Masullo
