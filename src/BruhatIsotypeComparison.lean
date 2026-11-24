import BruhatSchwartzTranslation
import BruhatSchwartzStructure
import CompactGroupAveraging
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Operator.Extend

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

section Source

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Left translation on the full Schwartz–Bruhat space. -/
def bruhatSchwartzTranslationAction : G →* (BruhatSchwartz G →L[ℂ] BruhatSchwartz G) where
  toFun := bruhatSchwartz_translate
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (bruhatSchwartz_translate (1 : G) f).val x = f.val x
    rw [bruhatSchwartz_translate_apply, inv_one, one_mul]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (bruhatSchwartz_translate (a * b) f).val x =
      (bruhatSchwartz_translate a (bruhatSchwartz_translate b f)).val x
    simp only [bruhatSchwartz_translate_apply, mul_inv_rev, mul_assoc]

set_option maxHeartbeats 900000 in
/-- Compact-subgroup averaging is a continuous endomorphism on the full
Schwartz–Bruhat space. Each orbit is integrated inside one elementary stage. -/
theorem exists_bruhatSchwartz_compactAverage (K : Subgroup G) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ω : PontryaginDual K) :
    ∃ P : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
      ∀ f, HasPositivePettisIntegral ν
        (fun k : K ↦ (((ω k)⁻¹ : Circle) : ℂ) • bruhatSchwartz_translate (k : G) f) (P f) := by
  let E := BruhatSchwartz G
  letI : UniformSpace E := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : T2Space E := bruhatSchwartz_t2
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let A := twistedCircleAction ω.toMonoidHom
    ((bruhatSchwartzTranslationAction (G := G)).comp K.subtype)
  have hω : Continuous (fun k : K ↦ (((ω k)⁻¹ : Circle) : ℂ)) :=
    continuous_subtype_val.comp ω.continuous.inv
  have hA : Continuous (fun z : K × E ↦ A z.1 z.2) :=
    (hω.comp continuous_fst).smul
      (continuous_bruhatSchwartz_translate.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  apply compactPettis_clm_of_exists ν A hA
  intro f
  obtain ⟨p, u, hu⟩ := f.property
  have hK : IsCompact (K : Set G) := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨q, hpq, hq⟩ := exists_stage_refinement_containing_compact p hK
  let z (k : K) : q.1.upper.val := ⟨(k : G)⁻¹, hq (K.inv_mem k.property)⟩
  let v : q.Space := p.transition q hpq u
  let g (k : K) : q.Space := (((ω k)⁻¹ : Circle) : ℂ) •
    elementarySchwartz_translate (q.1.stageCoordinates q.2 (z k)).toAdd v
  let W := elementarySchwartz_withSeminorms
    (m := q.2.realDim) (n := q.2.torusDim) (r := q.2.latticeRank) (F := q.2.finiteFactor)
  letI : ContinuousSMul ℂ q.Space := W.continuousSMul
  letI : LocallyConvexSpace ℝ q.Space := W.toLocallyConvexSpace
  letI : CompleteSpace q.Space := completeSpace_elementarySchwartz
  letI : QuasiCompleteSpace ℂ q.Space := inferInstance
  letI : T2Space q.Space := elementarySchwartz_t2
  have hz : Continuous z := continuous_subtype_val.inv.subtype_mk _
  have hcoord : Continuous (fun k ↦ (q.1.stageCoordinates q.2 (z k)).toAdd) :=
    continuous_toAdd.comp ((q.1.stageCoordinates q.2).continuous.comp hz)
  have hg : Continuous g := hω.smul
    (continuous_elementarySchwartz_translate.comp (hcoord.prodMk continuous_const))
  obtain ⟨x, hx⟩ := exists_positivePettisIntegral_of_hasCompactSupport ν hg
    (HasCompactSupport.of_compactSpace _)
  have he (k : K) : q.inclusionCLM (g k) = A k f := by
    change q.inclusionCLM ((((ω k)⁻¹ : Circle) : ℂ) •
      elementarySchwartz_translate (q.1.stageCoordinates q.2 (z k)).toAdd v) =
        (((ω k)⁻¹ : Circle) : ℂ) • bruhatSchwartz_translate (k : G) f
    rw [map_smul]
    congr 1
    apply Subtype.ext
    change q.realize _ = _
    rw [q.realize_translate]
    have hv : q.realize v = f.val :=
      (congrArg Subtype.val (p.inclusion_transition q hpq u)).trans hu
    rw [hv]
    rfl
  refine ⟨q.inclusionCLM x, fun ℓ ↦ ?_⟩
  have hcomp : (ℓ.comp q.inclusionCLM) ∘ g = ℓ ∘ (fun k ↦ A k f) :=
    funext fun k ↦ congrArg ℓ (he k)
  exact ⟨hcomp ▸ (hx (ℓ.comp q.inclusionCLM)).1,
    (hx (ℓ.comp q.inclusionCLM)).2.trans (congrArg (fun f : K → ℂ ↦ ∫ k, f k ∂ν) hcomp)⟩

end Source

section Comparison

variable {K X E : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X] [T2Space X] [PolynormableSpace ℂ X]
  [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [PolynormableSpace ℂ E]
  (ν : Measure K)

omit [CommGroup K] [IsTopologicalGroup K] [CompactSpace K] [IsUniformAddGroup X]
  [T2Space X] [PolynormableSpace ℂ X] [IsUniformAddGroup E] in
/-- Natural transformation of Pettis averages, including a measure-preserving
reparametrization of the compact group. -/
theorem compactAverage_intertwines
    (A : K → X →L[ℂ] X) (B : K → E →L[ℂ] E)
    (P : X →L[ℂ] X) (Q : E →L[ℂ] E)
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A k x) (P x))
    (hQ : ∀ u, HasPositivePettisIntegral ν (fun k ↦ B k u) (Q u))
    (i : X →L[ℂ] E) (β : K ≃ₜ K) (hβ : MeasurePreserving β ν ν)
    (hi : ∀ k x, i (A k x) = B (β k) (i x)) (x : X) :
    i (P x) = Q (i x) := by
  refine (weakBidualEval_isEmbedding E).injective ?_
  exact DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ ↦ by
    change ℓ (i (P x)) = ℓ (Q (i x))
    rw [show ℓ (i (P x)) = ∫ k, ℓ (i (A k x)) ∂ν from (hP x (ℓ.comp i)).2,
      show ℓ (Q (i x)) = ∫ k, ℓ (B k (i x)) ∂ν from (hQ (i x) ℓ).2]
    simp_rw [hi]
    exact hβ.integral_comp β.toMeasurableEquiv.measurableEmbedding (fun k : K ↦ ℓ (B k (i x)))

variable [ν.IsHaarMeasure] [IsProbabilityMeasure ν]

omit [CompactSpace K] [IsProbabilityMeasure ν] in
private theorem compactAverage_mem_fixed
    (A : K →* (X →L[ℂ] X)) (P : X →L[ℂ] X)
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A k x) (P x)) (x : X) :
    P x ∈ fixedSubmodule A := by
  intro g
  refine (weakBidualEval_isEmbedding X).injective ?_
  exact DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ X)) _ _ fun ℓ ↦ by
    change ℓ (A g (P x)) = ℓ (P x)
    rw [show ℓ (A g (P x)) = ∫ k, ℓ (A g (A k x)) ∂ν from (hP x (ℓ.comp (A g))).2,
      show ℓ (P x) = ∫ k, ℓ (A k x) ∂ν from (hP x ℓ).2]
    simp_rw [← show ∀ k, A (g * k) x = A g (A k x) from fun k ↦ by rw [map_mul]; rfl]
    exact integral_mul_left_eq_self (μ := ν) (fun k ↦ ℓ (A k x)) g

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K]
  [ν.IsHaarMeasure] in
private theorem compactAverage_of_fixed
    (A : K →* (X →L[ℂ] X)) (P : X →L[ℂ] X)
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A k x) (P x))
    {x : X} (hx : x ∈ fixedSubmodule A) : P x = x := by
  refine (weakBidualEval_isEmbedding X).injective ?_
  exact DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ X)) _ _ fun ℓ ↦ by
    change ℓ (P x) = ℓ x
    rw [show ℓ (P x) = ∫ k, ℓ (A k x) ∂ν from (hP x ℓ).2]
    simp [show ∀ k, A k x = x from hx, integral_const, measureReal_def]

/-- Normalized compact averages identify the kernel quotient with the
closed fixed space, with the quotient map given by averaging. -/
def compactAverage_quotientEquiv
    (A : K →* (X →L[ℂ] X)) (P : X →L[ℂ] X)
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A k x) (P x)) :
    (X ⧸ P.ker) ≃L[ℂ] fixedSubmodule A := by
  let F := P.codRestrict (fixedSubmodule A) (compactAverage_mem_fixed ν A P hP)
  let L := P.ker.liftQL F (fun x hx ↦ Subtype.ext (show P x = 0 from hx))
  let R := P.ker.mkQL.comp (fixedSubmodule A).subtypeL
  exact { toLinearEquiv := LinearEquiv.ofLinear L.toLinearMap R.toLinearMap
            (LinearMap.ext fun u ↦ Subtype.ext (compactAverage_of_fixed ν A P hP u.property))
            (LinearMap.ext fun u ↦ by
              obtain ⟨x, rfl⟩ := P.ker.mkQ_surjective u
              change P.ker.mkQ (P x) = P.ker.mkQ x
              apply (Submodule.Quotient.eq P.ker).mpr
              change P (P x - x) = 0
              rw [map_sub, compactAverage_of_fixed ν A P hP
                (compactAverage_mem_fixed ν A P hP x), sub_self])
          continuous_toFun := L.continuous
          continuous_invFun := R.continuous }

omit [CompactSpace K] in
/-- D.2.2.1(1)–(3). An equivariant injection pulls back both kernels and
fixed spaces. If its range is dense, both induced maps have dense range. -/
theorem compactAverage_compare
    (A : K →* (X →L[ℂ] X)) (B : K →* (E →L[ℂ] E))
    (P : X →L[ℂ] X) (Q : E →L[ℂ] E)
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A k x) (P x))
    (hQ : ∀ u, HasPositivePettisIntegral ν (fun k ↦ B k u) (Q u))
    (i : X →L[ℂ] E) (hi : Injective i) (he : ∀ k x, i (A k x) = B k (i x)) :
    Q.ker.comap i.toLinearMap = P.ker ∧ (fixedSubmodule B).comap i.toLinearMap = fixedSubmodule A ∧
    ∃ j : (X ⧸ P.ker) →L[ℂ] (E ⧸ Q.ker), ∃ l : fixedSubmodule A →L[ℂ] fixedSubmodule B,
      Injective j ∧ Injective l ∧ (∀ x, j (P.ker.mkQ x) = Q.ker.mkQ (i x)) ∧
      (∀ x, (l x : E) = i (x : X)) ∧ (DenseRange i → DenseRange j ∧ DenseRange l) := by
  have hPQ x : i (P x) = Q (i x) :=
    compactAverage_intertwines ν A B P Q hP hQ i (Homeomorph.refl K) (MeasurePreserving.id ν) he x
  have hker : Q.ker.comap i.toLinearMap = P.ker := by
    ext x
    change Q (i x) = 0 ↔ P x = 0
    rw [← hPQ, ← i.map_zero, hi.eq_iff]
  have hfix : (fixedSubmodule B).comap i.toLinearMap = fixedSubmodule A := by
    ext x
    change (∀ k, B k (i x) = i x) ↔ ∀ k, A k x = x
    simp only [← he, hi.eq_iff]
  let F := Q.ker.mkQL.comp i
  have hF : P.ker = F.ker := by
    rw [← hker]
    ext x
    change Q (i x) = 0 ↔ Q.ker.mkQ (i x) = 0
    exact (Submodule.Quotient.mk_eq_zero Q.ker).symm
  let j := P.ker.liftQL F hF.le
  let l : fixedSubmodule A →L[ℂ] fixedSubmodule B := i.restrict (fun x hx ↦ by
    change x ∈ (fixedSubmodule B).comap i.toLinearMap
    rwa [hfix])
  refine ⟨hker, hfix, j, l, ?_, ?_, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  · exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' P.ker F.toLinearMap hF)
  · intro x y h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  · intro hd
    constructor
    · apply DenseRange.of_comp (g := P.ker.mkQ)
      exact Q.ker.mkQ_surjective.denseRange.comp hd Q.ker.continuous_mkQ
    · let R := Q.codRestrict (fixedSubmodule B) (compactAverage_mem_fixed ν B Q hQ)
      have hR : Surjective R := fun x ↦ ⟨x.val, Subtype.ext (compactAverage_of_fixed ν B Q hQ x.property)⟩
      apply DenseRange.of_comp (g := P.codRestrict (fixedSubmodule A) (compactAverage_mem_fixed ν A P hP))
      have heq : l ∘ (P.codRestrict (fixedSubmodule A) (compactAverage_mem_fixed ν A P hP)) = R ∘ i :=
        funext fun x ↦ Subtype.ext (hPQ x)
      rw [heq]
      exact hR.denseRange.comp hd R.continuous

omit [IsUniformAddGroup X] [T2Space X] [PolynormableSpace ℂ X] [PolynormableSpace ℂ E] in
/-- The extension in D.2.2.1(4), using the subspace topology induced by the injection. -/
theorem denseContinuousLinear_extension [CompleteSpace E] [ContinuousConstSMul ℂ E]
    (i : X →L[ℂ] E) (hi : Injective i) (hd : DenseRange i) (T : X →L[ℂ] X)
    (hT : @Continuous X E (TopologicalSpace.induced i inferInstance) _ (fun x ↦ i (T x))) :
    ∃! U : E →L[ℂ] E, ∀ x, U (i x) = i (T x) := by
  let R := i.toLinearMap.range
  let e : X ≃ₗ[ℂ] R := LinearEquiv.ofInjective i.toLinearMap hi
  have hcont : @Continuous R X _ (TopologicalSpace.induced i inferInstance) e.symm := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.congr (fun x ↦ (congrArg Subtype.val (e.apply_symm_apply x)).symm)
  let F : R →L[ℂ] E :=
    ⟨(i.toLinearMap.comp T.toLinearMap).comp e.symm.toLinearMap,
      @Continuous.comp R X E _ (TopologicalSpace.induced i inferInstance) _
        e.symm (fun x ↦ i (T x)) hT hcont⟩
  have hdR : DenseRange R.subtypeL := by
    change Dense (range R.subtype)
    rw [← LinearMap.coe_range, Submodule.range_subtype]
    exact hd
  have huR : IsUniformInducing R.subtypeL := ⟨rfl⟩
  letI : IsUniformAddGroup R := huR.isUniformAddGroup R.subtypeL
  have hF (x : X) : F (e x) = i (T x) :=
    congrArg (fun y ↦ i (T y)) (e.symm_apply_apply x)
  refine ⟨F.extend R.subtypeL, fun x ↦ (F.extend_eq hdR huR (e x)).trans (hF x), ?_⟩
  intro U hU
  refine (F.extend_unique hdR huR U (ContinuousLinearMap.ext ?_)).symm
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact (hU y).trans (hF y).symm

omit [CompactSpace K] in
/-- The averaging intertwiners descend on the quotients and restrict to
the fixed subspaces. Both maps commute with the quotient-to-fixed equivalences. -/
theorem compactAverage_descend
    (A A' : K →* (X →L[ℂ] X)) (P P' T : X →L[ℂ] X)
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A k x) (P x))
    (hP' : ∀ x, HasPositivePettisIntegral ν (fun k ↦ A' k x) (P' x))
    (h : ∀ x, T (P x) = P' (T x)) :
    ∃! w : ((X ⧸ P.ker) →L[ℂ] (X ⧸ P'.ker)) × (fixedSubmodule A →L[ℂ] fixedSubmodule A'),
      (∀ x, w.1 (P.ker.mkQ x) = P'.ker.mkQ (T x)) ∧
      (∀ x, (w.2 x : X) = T (x : X)) ∧
      ∀ y, compactAverage_quotientEquiv ν A' P' hP' (w.1 y) =
        w.2 (compactAverage_quotientEquiv ν A P hP y) := by
  let D := P.ker.liftQL (P'.ker.mkQL.comp T) (fun x hx ↦ by
    change P x = 0 at hx
    apply (Submodule.Quotient.mk_eq_zero P'.ker).mpr
    change P' (T x) = 0
    rw [← h, hx, map_zero])
  let R : fixedSubmodule A →L[ℂ] fixedSubmodule A' := T.restrict (fun x hx ↦ by
    rw [← compactAverage_of_fixed ν A P hP hx, h]
    exact compactAverage_mem_fixed ν A' P' hP' (T x))
  refine ⟨⟨D, R⟩, ⟨fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := P.ker.mkQ_surjective y
    exact Subtype.ext (h x).symm
  · intro w hw
    apply Prod.ext <;> apply ContinuousLinearMap.ext
    · exact P.ker.mkQ_surjective.forall.mpr hw.1
    · exact fun x ↦ Subtype.ext (hw.2.1 x)

end Comparison

section Covariance

variable {G X E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X] [T2Space X]
  [PolynormableSpace ℂ X] [ContinuousSMul ℂ X]
  [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
  [PolynormableSpace ℂ E]

/-- The action whose fixed subspace is the specified compact isotype. -/
def compactIsotypicAction (ω : PontryaginDual K) (ρ : G →* (X →L[ℂ] X)) :
    K →* (X →L[ℂ] X) :=
  twistedCircleAction ω.toMonoidHom (ρ.comp K.subtype)

/-- A modulus-preserving automorphism acts on its compact kernel. -/
def compactKernelAutomorphism (α : G ≃ₜ* G)
    (hα : ∀ g, α g ∈ K ↔ g ∈ K) : K ≃ₜ* K where
  toFun k := ⟨α k.val, (hα k.val).mpr k.property⟩
  invFun k := ⟨α.symm k.val, (hα (α.symm k.val)).mp (by simp)⟩
  left_inv k := Subtype.ext (α.symm_apply_apply k.val)
  right_inv k := Subtype.ext (α.apply_symm_apply k.val)
  map_mul' k l := Subtype.ext (map_mul α k.val l.val)
  continuous_toFun := (α.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (α.symm.continuous.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] [T2Space X] [PolynormableSpace ℂ X]
  [ContinuousSMul ℂ X] [PolynormableSpace ℂ E] in
/-- The extension inherits covariance on the whole group by density. -/
theorem dense_extension_covariant
    (A : G →* (X →L[ℂ] X)) (B : G →* (E →L[ℂ] E))
    (i : X →L[ℂ] E) (hi : DenseRange i) (he : ∀ g x, i (A g x) = B g (i x))
    (α : G ≃ₜ* G) (T : X →L[ℂ] X) (U : E →L[ℂ] E)
    (hU : ∀ x, U (i x) = i (T x)) (hT : ∀ g x, T (A g x) = A (α g) (T x)) :
    ∀ g u, U (B g u) = B (α g) (U u) := by
  intro g u
  refine hi.induction_on u
    (isClosed_eq (U.continuous.comp (B g).continuous)
      ((B (α g)).continuous.comp U.continuous)) ?_
  intro x
  rw [← he, hU, hT, he, hU]

/-- A covariant operator carries the average for the original character to
the average for that character composed with the inverse automorphism. -/
theorem compactIsotypicAverage_covariant
    (ν : Measure K) [ν.IsHaarMeasure]
    (A : G →* (X →L[ℂ] X)) (α : G ≃ₜ* G) (hα : ∀ g, α g ∈ K ↔ g ∈ K)
    (ω : PontryaginDual K) (T P P' : X →L[ℂ] X)
    (hT : ∀ g x, T (A g x) = A (α g) (T x))
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ compactIsotypicAction K ω A k x) (P x))
    (hP' : ∀ x, HasPositivePettisIntegral ν
      (fun k ↦ compactIsotypicAction K (ω.comp ⟨(compactKernelAutomorphism K α hα).symm.toMonoidHom,
        (compactKernelAutomorphism K α hα).symm.continuous⟩) A k x)
      (P' x)) :
    ∀ x, T (P x) = P' (T x) := by
  let β := compactKernelAutomorphism K α hα
  let χ : PontryaginDual K := ω.comp ⟨β.symm.toMonoidHom, β.symm.continuous⟩
  have hβ : MeasurePreserving β ν ν :=
    β.toMonoidHom.measurePreserving β.continuous β.surjective rfl
  apply compactAverage_intertwines ν (compactIsotypicAction K ω A) (compactIsotypicAction K χ A)
    P P' hP hP' T β.toHomeomorph hβ
  intro k x
  change T ((((ω k)⁻¹ : Circle) : ℂ) • A k.val x) =
    (((χ (β k))⁻¹ : Circle) : ℂ) • A (α k.val) (T x)
  have hχ : χ (β k) = ω k := congrArg ω (β.symm_apply_apply k)
  rw [map_smul, hT, hχ]

end Covariance

section Extension

variable {G X E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X] [T2Space X]
  [PolynormableSpace ℂ X] [ContinuousSMul ℂ X]
  [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
  [PolynormableSpace ℂ E] [ContinuousSMul ℂ E] [CompleteSpace E]

/-- D.2.2.1(4). The unique dense extension is covariant on the full group
and intertwines the averages for the two related compact isotypes. -/
theorem compactIsotypicAverage_extend
    (ν : Measure K) [ν.IsHaarMeasure]
    (A : G →* (X →L[ℂ] X)) (B : G →* (E →L[ℂ] E))
    (i : X →L[ℂ] E) (hi : Injective i) (hd : DenseRange i)
    (he : ∀ g x, i (A g x) = B g (i x))
    (α : G ≃ₜ* G) (hα : ∀ g, α g ∈ K ↔ g ∈ K)
    (ω : PontryaginDual K) (T P P' : X →L[ℂ] X) (Q Q' : E →L[ℂ] E)
    (hTcont : @Continuous X E (TopologicalSpace.induced i inferInstance) _ (fun x ↦ i (T x)))
    (hT : ∀ g x, T (A g x) = A (α g) (T x))
    (hP : ∀ x, HasPositivePettisIntegral ν (fun k ↦ compactIsotypicAction K ω A k x) (P x))
    (hQ : ∀ u, HasPositivePettisIntegral ν (fun k ↦ compactIsotypicAction K ω B k u) (Q u))
    (hP' : let β := compactKernelAutomorphism K α hα
      let χ := ω.comp ⟨β.symm.toMonoidHom, β.symm.continuous⟩
      ∀ x, HasPositivePettisIntegral ν (fun k ↦ compactIsotypicAction K χ A k x) (P' x))
    (hQ' : let β := compactKernelAutomorphism K α hα
      let χ := ω.comp ⟨β.symm.toMonoidHom, β.symm.continuous⟩
      ∀ u, HasPositivePettisIntegral ν (fun k ↦ compactIsotypicAction K χ B k u) (Q' u)) :
    (∀ x, T (P x) = P' (T x)) ∧
    ∃! U : E →L[ℂ] E, (∀ x, U (i x) = i (T x)) ∧
      (∀ g u, U (B g u) = B (α g) (U u)) ∧ (∀ u, U (Q u) = Q' (U u)) := by
  have hTP := compactIsotypicAverage_covariant K ν A α hα ω T P P' hT hP hP'
  obtain ⟨U, hU, huniq⟩ := denseContinuousLinear_extension i hi hd T hTcont
  have hCov := dense_extension_covariant A B i hd he α T U hU hT
  have hUQ := compactIsotypicAverage_covariant K ν B α hα ω U Q Q' hCov hQ hQ'
  exact ⟨hTP, U, ⟨hU, hCov, hUQ⟩, fun V hV ↦ huniq V hV.1⟩

end Extension

section BruhatComparison

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [T2Space E] [PolynormableSpace ℂ E] [CompleteSpace E]
  [ContinuousSMul ℂ E]

local notation "S" => BruhatSchwartz G
local notation "ρS" => bruhatSchwartzTranslationAction (G := G)

local instance : UniformSpace S := bruhatSchwartzUniformSpace
local instance : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
local instance : T2Space S := bruhatSchwartz_t2
local instance : ContinuousSMul ℂ S := (PolynormableSpace.withSeminorms ℂ S).continuousSMul

/-- D.2.2.1(1)–(3) on the actual Schwartz–Bruhat space. The compact subgroup
can be the kernel of any modulus as in the manuscript. Both averages use
the probability normalization of the given Haar measure. -/
theorem bruhatIsotypeComparison
    (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsHaarMeasure] (ω : PontryaginDual K)
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (i : S →L[ℂ] E) (hi : Injective i) (he : ∀ g f, i (ρS g f) = ρ g (i f)) :
    let A := compactIsotypicAction K ω ρS
    let B := compactIsotypicAction K ω ρ
    let ν := (μ univ)⁻¹ • μ
    ∃ (P : S →L[ℂ] S) (Q : E →L[ℂ] E),
      (∀ f, HasPositivePettisIntegral ν (fun k ↦ A k f) (P f)) ∧
      (∀ u, HasPositivePettisIntegral ν (fun k ↦ B k u) (Q u)) ∧
      Q.ker.comap i.toLinearMap = P.ker ∧
      (fixedSubmodule B).comap i.toLinearMap = fixedSubmodule A ∧
      IsClosed (P.ker : Set S) ∧ IsClosed (fixedSubmodule A : Set S) ∧
      ∃ j : (S ⧸ P.ker) →L[ℂ] (E ⧸ Q.ker), ∃ l : fixedSubmodule A →L[ℂ] fixedSubmodule B,
      Injective j ∧ Injective l ∧ (∀ f, j (P.ker.mkQ f) = Q.ker.mkQ (i f)) ∧
      (∀ f, (l f : E) = i (f : S)) ∧ (DenseRange i → DenseRange j ∧ DenseRange l) := by
  dsimp only
  let ν : Measure K := (μ univ)⁻¹ • μ
  letI : IsProbabilityMeasure ν := inferInstance
  letI : ν.IsHaarMeasure := Measure.IsHaarMeasure.smul μ
    (ENNReal.inv_ne_zero.mpr (measure_ne_top μ univ)) (ENNReal.inv_ne_top.mpr (NeZero.ne (μ univ)))
  letI : Module ℝ E := Module.restrictScalars ℝ ℂ E
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  letI : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let A := compactIsotypicAction K ω ρS
  let B := compactIsotypicAction K ω ρ
  obtain ⟨P, hP⟩ := exists_bruhatSchwartz_compactAverage K ν ω
  have hρK := hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_snd : Continuous (Prod.snd : K × E → E)))
  obtain ⟨_, Q, hQ, _⟩ := compactGroupIsotypicAverage (ρ.comp K.subtype) hρK
    ω.toMonoidHom ω.continuous ν
  have hab (k : K) (f : S) : i (A k f) = B k (i f) := by
    change i ((((ω k)⁻¹ : Circle) : ℂ) • ρS k.val f) =
      (((ω k)⁻¹ : Circle) : ℂ) • ρ k.val (i f)
    rw [map_smul, he]
  obtain ⟨hk, hf, hj⟩ := compactAverage_compare ν A B P Q hP hQ i hi hab
  exact ⟨P, Q, hP, hQ, hk, hf, P.isClosed_ker, fixedSubmodule_isClosed A, hj⟩

end BruhatComparison

end

end Masullo
