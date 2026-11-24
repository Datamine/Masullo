import SLocalThetaDualGeneration
import AdelicPolarDistributions
import AdelicBruhatStructure
import CompactGroupAveraging
import CompactCharacterCompleteness

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev E := GlobalBruhat F
private abbrev K := normOneIdeleClass F
private abbrev Θ := GlobalThetaQuotient F
private abbrev N := (globalThetaOperator F).ker

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

/-- Bounded S-local theta classes admit compact test covers in the same place set. -/
theorem sLocalTheta_bounded_lift (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Set (SLocalThetaQuotient F S)) (hB : IsVonNBounded ℂ B) :
    ∃ C : Set (sLocalBruhatImage F S), IsCompact C ∧
      B ⊆ (sLocalThetaOperator F S).ker.mkQL '' C := by
  letI : T2Space (SLocalThetaQuotient F S) := sLocalThetaQuotient_t2Space F S
  letI : PolynormableSpace ℂ (SLocalThetaQuotient F S) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  obtain ⟨W, D, hF, hE, hT, hFinal, hN, _, hL⟩ := sLocalTheta_exists_strictFrechet_with_lifts F S
  have hArch := archimedeanSchwartz_nuclear F
  letI : ∀ n, PolynormableSpace ℂ (W n) := fun n ↦ (hN hArch n).2.1
  letI : ∀ n, IsTopologicalAddGroup (W n) := fun n ↦ (hF n).choose
  obtain ⟨n, C, hC, hCB⟩ := (D.strict_bounded_iff hT (fun n ↦ (hE n).isEmbedding)
    (fun L h ↦ by
      apply (norm_withSeminorms ℂ _).continuous_of_continuous_comp L
      intro i
      apply hFinal
      intro n
      exact ((norm_withSeminorms ℂ _).continuous_seminorm i).comp (h n)) B).mp hB
  rw [← hCB]
  exact hL hArch n C hC

/-- Every bounded family of global theta classes admits a compact cover upstairs. -/
theorem globalTheta_bounded_lift (B : Set (Θ F)) (hB : IsVonNBounded ℂ B) :
    ∃ C : Set (E F), IsCompact C ∧ B ⊆ (N F).mkQL '' C := by
  obtain ⟨S, A, hA, hAB⟩ := (globalThetaQuotient_bounded_iff F B).mp hB
  obtain ⟨C, hC, hcover⟩ := sLocalTheta_bounded_lift F S A hA
  refine ⟨Subtype.val '' C, hC.image continuous_subtype_val, ?_⟩
  rw [← hAB]
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨f, hf, rfl⟩ := hcover hq
  exact ⟨f.val, ⟨f, hf, rfl⟩, rfl⟩

/-- The ordinary global transpose in the topology of bounded convergence. -/
def globalThetaTranspose : StrongDual ℂ (Θ F) →L[ℂ] StrongDual ℂ (E F) :=
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ (N F).mkQL

theorem globalThetaTranspose_isEmbedding : IsEmbedding (globalThetaTranspose F) := by
  apply quotientDual_strongEmbedding_of_bounded_lifts
  intro B hB
  obtain ⟨C, hC, hCB⟩ := globalTheta_bounded_lift F B hB
  exact ⟨C, hC.isVonNBounded ℂ, hCB⟩

theorem globalThetaTranspose_invariant (T : StrongDual ℂ (Θ F)) (g : Idele F)
    (hg : ideleClassMap F g = 1) (f : E F) :
    globalThetaTranspose F T (GlobalBruhat.leftTranslate F g f) = globalThetaTranspose F T f := by
  change T (Submodule.Quotient.mk (GlobalBruhat.leftTranslate F g f)) = T (Submodule.Quotient.mk f)
  rw [← globalThetaTranslateIdeles_mk, ← globalThetaTranslate_class, hg, globalThetaTranslate_one]
  rfl

theorem globalThetaInvariantDistributions_isClosed :
    IsClosed {T : StrongDual ℂ (E F) | ∀ g : Idele F, ideleClassMap F g = 1 →
      ∀ f, T (GlobalBruhat.leftTranslate F g f) = T f} := by
  let G := {g : Idele F | ideleClassMap F g = 1}
  rw [show {T : StrongDual ℂ (E F) | ∀ g : Idele F, ideleClassMap F g = 1 →
      ∀ f, T (GlobalBruhat.leftTranslate F g f) = T f} =
      ⋂ (g : G) (f : E F), {T : StrongDual ℂ (E F) |
        T (GlobalBruhat.leftTranslate F g.val f) = T f} from by ext T; simp [G]]
  exact isClosed_iInter fun g ↦ isClosed_iInter fun f ↦
    isClosed_eq (continuous_eval_const _) (continuous_eval_const _)

variable (μ : Measure (Idele F)) [μ.IsHaarMeasure]

private abbrev line (y : ℝ) : ℂ := 2 + (y : ℂ) * Complex.I

/-- Mellin evaluation on the global line of absolute convergence `Re s = 2`. -/
def globalThetaLineTestEval (ω : PontryaginDual (K F)) (y : ℝ) : StrongDual ℂ (E F) :=
  idelicZetaCLM F μ (compactIdeleClassCharacter F ω)
    (compactIdeleClassCharacter_unitary F ω) (line y) (by norm_num)

theorem globalThetaLineTestEval_translate (ω : PontryaginDual (K F)) (y : ℝ)
    (g : Idele F) (f : E F) :
    globalThetaLineTestEval F μ ω y (GlobalBruhat.leftTranslate F g f) =
      (ideleNormTwist F (compactIdeleClassCharacter F ω) (line y) (ideleClassMap F g) : ℂ) *
        globalThetaLineTestEval F μ ω y f := by
  simp only [globalThetaLineTestEval, idelicZetaCLM_apply, idelicZetaIntegral_leftTranslate]

private theorem globalThetaLineTestEval_translate_normOne (ω : PontryaginDual (K F)) (y : ℝ)
    (k : K F) (g : Idele F) (hg : ideleClassMap F g = k.val) (f : E F) :
    globalThetaLineTestEval F μ ω y (GlobalBruhat.leftTranslate F g f) =
      (ω k : ℂ) * globalThetaLineTestEval F μ ω y f := by
  rw [globalThetaLineTestEval_translate, hg]
  have hk : ideleClassNorm F k.val = 1 := k.property
  change ((compactIdeleClassCharacter F ω k.val : ℂ) * ideleNormPower F (line y) k.val) * _ = _
  rw [compactIdeleClassCharacter_apply_normOne, ideleNormPower, hk]
  simp

private theorem globalThetaLine_ker (f : E F) :
    f ∈ N F ↔ ∀ (ω : PontryaginDual (K F)) y, globalThetaLineTestEval F μ ω y f = 0 := by
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  letI := hν
  have he := (globalIdelicZetaKernels_eq_theta F μ ν hW f).1
  have hker : f ∈ globalIdelicZetaKernel F μ ↔ f ∈ N F := by
    rw [he, LinearMap.mem_ker]
    exact ⟨fun h ↦ funext h, fun h q ↦ congrFun h q⟩
  rw [← hker, globalIdelicZetaKernel, Submodule.mem_iInf]
  simp only [globalIdelicZetaComponentKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

private theorem globalThetaTest_span_eq {ι : Type*} (l : ι → StrongDual ℂ (E F))
    (M : Submodule ℂ (E F)) (hM : ∀ f, f ∈ M ↔ ∀ i, l i f = 0) :
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ (E F))) =
      {T : StrongDual ℂ (E F) | ∀ f ∈ M, T f = 0} := by
  letI : UniformSpace (E F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E F) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (E F) := globalBruhat_complete F
  letI : BarrelledSpace ℂ (E F) := globalBruhat_barrelled F
  letI : PolynormableSpace ℂ (E F) := (globalBruhat_nuclear F).2.1
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (globalBruhat_nuclear F)
  exact strongDual_closure_span_eq_annihilator e he l M hM

/-- On the ordinary global quotient one Mellin line per component suffices,
and every nowhere-zero normalization gives the same strongly closed span. -/
theorem globalThetaTranspose_range_line (d : PontryaginDual (K F) × ℝ → ℂ) (hd : ∀ i, d i ≠ 0) :
    range (globalThetaTranspose F) =
      closure (Submodule.span ℂ (range fun i : PontryaginDual (K F) × ℝ ↦
        d i • globalThetaLineTestEval F μ i.1 i.2) : Set (StrongDual ℂ (E F))) := by
  let l (i : PontryaginDual (K F) × ℝ) := d i • globalThetaLineTestEval F μ i.1 i.2
  have hM (f : E F) : f ∈ N F ↔ ∀ i, l i f = 0 := by
    rw [globalThetaLine_ker F μ f]
    constructor
    · intro h i
      change d i * globalThetaLineTestEval F μ i.1 i.2 f = 0
      rw [h, mul_zero]
    · intro h ω y
      exact (mul_eq_zero.mp (h (ω,y))).resolve_left (hd (ω,y))
  change range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ (N F).mkQL) =
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ (E F)))
  rw [quotientDual_strongRange, globalThetaTest_span_eq F l (N F) hM]

variable (ω : PontryaginDual (K F))

private abbrev M := globalIdelicZetaComponentKernel F μ ω

private theorem globalThetaComponent_ker (f : E F) :
    f ∈ M F μ ω ↔ ∀ y, globalThetaLineTestEval F μ ω y f = 0 := by
  simp only [M, globalIdelicZetaComponentKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

theorem globalThetaComponent_ker_eq (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν)) :
    M F μ ω = (globalHomogeneousThetaOperator F ν ω).ker := by
  ext f
  rw [LinearMap.mem_ker]
  exact ((globalIdelicZetaKernels_eq_theta F μ ν hν f).2 ω).trans
    ⟨fun h ↦ funext h, fun h k ↦ congrFun h k⟩

/-- Quotient Mellin evaluation of the ordinary theta class. -/
def globalThetaLineEval (y : ℝ) : StrongDual ℂ (Θ F) :=
  (N F).liftQL (globalThetaLineTestEval F μ ω y) fun f hf ↦
    (globalThetaLine_ker F μ f).mp hf ω y

private theorem globalThetaLineEval_separates (q : Θ F)
    (h : ∀ τ y, globalThetaLineEval F μ τ y q = 0) : q = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F) q
  exact (Submodule.Quotient.mk_eq_zero _).mpr <| (globalThetaLine_ker F μ f).mpr h

/-- The norm-one idele class action on ordinary global theta classes. -/
def globalThetaNormOneAction : K F →* (Θ F →L[ℂ] Θ F) where
  toFun k := globalThetaTranslate F k.val
  map_one' := globalThetaTranslate_one F
  map_mul' k l := globalThetaTranslate_mul F k.val l.val

private theorem globalThetaLineEval_translate (y : ℝ) (k : K F) (q : Θ F) :
    globalThetaLineEval F μ ω y (globalThetaNormOneAction F k q) =
      (ω k : ℂ) * globalThetaLineEval F μ ω y q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F) q
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F k.val
  change globalThetaLineEval F μ ω y (globalThetaTranslate F k.val
    (Submodule.Quotient.mk f)) = _
  rw [← hg, globalThetaTranslate_class, globalThetaTranslateIdeles_mk]
  exact globalThetaLineTestEval_translate_normOne F μ ω y k g hg f

set_option maxHeartbeats 3000000 in
private theorem globalTheta_isotype_projection (ν : Measure (K F)) [ν.IsHaarMeasure] :
    ∃ P : Θ F →L[ℂ] Θ F,
      (∀ q, P q = q ↔ ∀ k, globalThetaNormOneAction F k q = (ω k : ℂ) • q) ∧
      (∀ q k, globalThetaNormOneAction F k (P q) = (ω k : ℂ) • P q) ∧
      (∀ (τ : PontryaginDual (K F)) (y : ℝ) (q : Θ F),
        globalThetaLineEval F μ τ y (P q) =
          if ω = τ then globalThetaLineEval F μ τ y q else 0) ∧
      ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • globalThetaNormOneAction F k q)
        ((ν.real univ : ℂ) • P q) := by
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  letI : UniformSpace (Θ F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Θ F) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Θ F) := globalThetaQuotient_complete F
  letI : T2Space (Θ F) := globalThetaQuotient_t2Space F
  letI : PolynormableSpace ℂ (Θ F) := polynormableSpace_complex_quotient (N F)
  letI : Module ℝ (Θ F) := Module.restrictScalars ℝ ℂ (Θ F)
  letI : IsScalarTower ℝ ℂ (Θ F) := IsScalarTower.restrictScalars ℝ ℂ (Θ F)
  letI : LocallyConvexSpace ℝ (Θ F) :=
    (PolynormableSpace.withSeminorms ℂ (Θ F)).toLocallyConvexSpace
  have hρ : Continuous (fun z : K F × Θ F ↦ globalThetaNormOneAction F z.1 z.2) :=
    (continuous_globalThetaTranslate F).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hfixed, P, hP, hRange, _, hProj, _⟩ := compactGroupIsotypicAverage (globalThetaNormOneAction F) hρ
    ω.toMonoidHom (map_continuous ω) ν
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    have hp := Measure.measure_pos_of_nonempty_interior (s := (univ : Set (K F))) ν (by simp)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)).ne'
  let A := (ν.real univ : ℂ)⁻¹ • P
  have hEig (q : Θ F) (k : K F) :
      globalThetaNormOneAction F k (A q) = (ω k : ℂ) • A q := by
    have hmem : P q ∈ range P := mem_range_self q
    rw [hRange] at hmem
    have h := (hfixed (P q)).mp hmem k
    change globalThetaNormOneAction F k ((ν.real univ : ℂ)⁻¹ • P q) =
      (ω k : ℂ) • ((ν.real univ : ℂ)⁻¹ • P q)
    rw [map_smul, h, smul_comm]
    rfl
  refine ⟨A, fun q ↦ ⟨?_, ?_⟩, hEig, (fun τ y q ↦ ?_), ?_⟩
  · intro h k
    simpa only [h] using hEig q k
  · intro he
    have hq : q ∈ range P := by rw [hRange]; exact (hfixed q).mpr he
    obtain ⟨x, rfl⟩ := hq
    have hx : A (A x) = A x := hProj x
    change A ((ν.real univ : ℂ)⁻¹ • P x) = (ν.real univ : ℂ)⁻¹ • P x at hx
    rw [map_smul] at hx
    exact (smul_right_injective _ (inv_ne_zero hmass)) hx
  · let L := globalThetaLineEval F μ τ y
    have h := (hP q L).2
    change L (P q) = ∫ k, L ((((ω k)⁻¹ : Circle) : ℂ) • globalThetaNormOneAction F k q) ∂ν at h
    have hval (k : K F) :
        L ((((ω k)⁻¹ : Circle) : ℂ) • globalThetaNormOneAction F k q) =
          (star (ω k : ℂ) * (τ k : ℂ)) * L q := by
      rw [map_smul, Circle.coe_inv_eq_conj, smul_eq_mul, mul_assoc]
      rw [globalThetaLineEval_translate F μ τ y]
      rfl
    rw [integral_congr_ae (ae_of_all ν hval), integral_mul_const,
      integral_character_pair ν ω τ] at h
    change L ((ν.real univ : ℂ)⁻¹ • P q) = if ω = τ then L q else 0
    rw [map_smul, smul_eq_mul, h]
    split_ifs <;> simp [hmass]

  · intro q
    change HasPositivePettisIntegral ν _ ((ν.real univ : ℂ) • ((ν.real univ : ℂ)⁻¹ • P q))
    rw [smul_smul, mul_inv_cancel₀ hmass, one_smul]
    exact hP q

/-- The natural map from ordinary theta classes to the specified character quotient. -/
def globalThetaToComponent : Θ F →L[ℂ] (E F ⧸ M F μ ω) :=
  (N F).liftQL (M F μ ω).mkQL fun f hf ↦ (Submodule.Quotient.mk_eq_zero _).mpr <|
    (globalThetaComponent_ker F μ ω f).mpr ((globalThetaLine_ker F μ f).mp hf ω)

/-- The product of the global homogeneous quotient maps. -/
def globalThetaToAllComponents : Θ F →L[ℂ] (∀ τ : PontryaginDual (K F), E F ⧸ M F μ τ) :=
  ContinuousLinearMap.pi (globalThetaToComponent F μ)

theorem globalThetaToAllComponents_injective : Injective (globalThetaToAllComponents F μ) := by
  intro q r h
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F) q
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (N F) r
  apply (Submodule.Quotient.eq (N F)).mpr
  apply (globalThetaLine_ker F μ (f - g)).mpr
  intro τ
  have hτ : (Submodule.Quotient.mk f : E F ⧸ M F μ τ) = Submodule.Quotient.mk g :=
    congrFun h τ
  exact (globalThetaComponent_ker F μ τ (f - g)).mp ((Submodule.Quotient.eq _).mp hτ)

theorem globalThetaToComponent_normOne (k : K F) (q : Θ F) :
    globalThetaToComponent F μ ω (globalThetaNormOneAction F k q) =
      (ω k : ℂ) • globalThetaToComponent F μ ω q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F) q
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F k.val
  change globalThetaToComponent F μ ω (globalThetaTranslate F k.val (Submodule.Quotient.mk f)) = _
  rw [← hg, globalThetaTranslate_class, globalThetaTranslateIdeles_mk]
  change (M F μ ω).mkQ (GlobalBruhat.leftTranslate F g f) = (ω k : ℂ) • (M F μ ω).mkQ f
  rw [← map_smul]
  change (Submodule.Quotient.mk _ : E F ⧸ M F μ ω) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, globalThetaComponent_ker]
  intro y
  rw [map_sub, globalThetaLineTestEval_translate_normOne F μ ω y k g hg,
    map_smul, smul_eq_mul, sub_self]

section IsotypeQuotient

variable {G V Q : Type*}
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V]
  [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]

/-- Simultaneous eigenspace for a prescribed character. -/
def thetaCharacterSubspace (ρ : G → V →L[ℂ] V) (χ : G → ℂ) : Submodule ℂ V :=
  ⨅ k : G, (ρ k - χ k • (ContinuousLinearMap.id ℂ V)).ker

omit [T2Space V] in
theorem mem_thetaCharacterSubspace (ρ : G → V →L[ℂ] V) (χ : G → ℂ) (v : V) :
    v ∈ thetaCharacterSubspace ρ χ ↔ ∀ k, ρ k v = χ k • v := by
  simp [thetaCharacterSubspace, LinearMap.mem_ker, sub_eq_zero]

theorem isClosed_thetaCharacterSubspace (ρ : G → V →L[ℂ] V) (χ : G → ℂ) :
    IsClosed (thetaCharacterSubspace ρ χ : Set V) := by
  rw [show (thetaCharacterSubspace ρ χ : Set V) = ⋂ k, {v | ρ k v = χ k • v} by
    ext v
    simp [mem_thetaCharacterSubspace]]
  exact isClosed_iInter fun k ↦ isClosed_eq (ρ k).continuous (continuous_const.smul continuous_id)

namespace ContinuousLinearMap

/-- A continuous section fixing the simultaneous eigenspace induces a topological
isomorphism onto it, with any nonzero scalar normalization. -/
def equivThetaCharacterSubspace (ρ : G → V →L[ℂ] V) (χ : G → ℂ)
    (p : V →L[ℂ] Q) (s : Q →L[ℂ] V) (hs : LeftInverse p s)
    (hEig : ∀ q k, ρ k (s q) = χ k • s q)
    (hFix : ∀ v, (∀ k, ρ k v = χ k • v) → s (p v) = v)
    (a : ℂˣ) : Q ≃L[ℂ] thetaCharacterSubspace ρ χ := by
  let f := s.codRestrict (thetaCharacterSubspace ρ χ) fun q ↦
    (mem_thetaCharacterSubspace ρ χ (s q)).mpr (hEig q)
  let g := p.comp (thetaCharacterSubspace ρ χ).subtypeL
  exact (ContinuousLinearEquiv.equivOfInverse f g hs (fun v ↦ Subtype.ext
    (hFix v.val ((mem_thetaCharacterSubspace ρ χ v.val).mp v.property)))).trans
      (ContinuousLinearEquiv.smulLeft a)

@[simp] theorem equivThetaCharacterSubspace_apply (ρ : G → V →L[ℂ] V) (χ : G → ℂ)
    (p : V →L[ℂ] Q) (s : Q →L[ℂ] V) (hs : LeftInverse p s)
    (hEig : ∀ q k, ρ k (s q) = χ k • s q)
    (hFix : ∀ v, (∀ k, ρ k v = χ k • v) → s (p v) = v)
    (a : ℂˣ) (q : Q) :
    (equivThetaCharacterSubspace ρ χ p s hs hEig hFix a q : V) = (a : ℂ) • s q := rfl

end ContinuousLinearMap

end IsotypeQuotient

/-- The ordinary-to-homogeneous global theta map is an open quotient map. -/
theorem globalThetaToComponent_isOpenMap : IsOpenMap (globalThetaToComponent F μ ω) :=
  IsOpenMap.of_comp (N F).mkQL.continuous (Submodule.Quotient.mk_surjective (N F))
    (M F μ ω).isOpenQuotientMap_mkQL.isOpenMap

/-- Haar averages on ordinary theta factor through the global homogeneous quotient. -/
theorem globalThetaComponent_pettisSection (ν : Measure (K F)) [ν.IsHaarMeasure] :
    ∃ s : (E F ⧸ M F μ ω) →L[ℂ] Θ F,
      LeftInverse (globalThetaToComponent F μ ω) s ∧
      (∀ q, s (globalThetaToComponent F μ ω q) = q ↔
        ∀ k, globalThetaNormOneAction F k q = (ω k : ℂ) • q) ∧
      (∀ q k, globalThetaNormOneAction F k (s q) = (ω k : ℂ) • s q) ∧
      ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • globalThetaNormOneAction F k q)
        ((ν.real univ : ℂ) • s (globalThetaToComponent F μ ω q)) := by
  obtain ⟨P, hFix, hEig, hP, hPettis⟩ := globalTheta_isotype_projection F μ ω ν
  let A := P.comp (N F).mkQL
  have hA : M F μ ω ≤ A.ker := by
    intro f hf
    apply globalThetaLineEval_separates F μ (A f)
    intro τ y
    change globalThetaLineEval F μ τ y (P ((N F).mkQL f)) = 0
    rw [hP]
    split_ifs with he
    · subst τ
      exact (globalThetaComponent_ker F μ ω f).mp hf y
    · rfl
  let s := (M F μ ω).liftQL A hA
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (M F μ ω) q
    obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective (N F) (A f)
    change globalThetaToComponent F μ ω (A f) = Submodule.Quotient.mk f
    rw [← hg]
    change (Submodule.Quotient.mk g : E F ⧸ M F μ ω) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    apply (globalThetaComponent_ker F μ ω (g - f)).mpr
    intro y
    have he := congrArg (globalThetaLineEval F μ ω y) hg
    change globalThetaLineTestEval F μ ω y g =
      globalThetaLineEval F μ ω y (P ((N F).mkQL f)) at he
    rw [hP, ite_eq_left rfl] at he
    rw [map_sub, sub_eq_zero]
    exact he
  · intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F) q
    exact hFix ((N F).mkQL f)
  · intro q k
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (M F μ ω) q
    exact hEig ((N F).mkQL f) k

  · intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F) q
    exact hPettis ((N F).mkQL f)

/-- The unnormalized global Pettis map is an open surjection onto the closed
character subspace, induced by a topological isomorphism from the actual quotient. -/
theorem globalThetaComponent_pettisEquiv (ν : Measure (K F)) [ν.IsHaarMeasure] :
    ∃ e : (E F ⧸ M F μ ω) ≃L[ℂ]
        thetaCharacterSubspace (globalThetaNormOneAction F) (fun k ↦ (ω k : ℂ)),
      IsOpenMap (e ∘ globalThetaToComponent F μ ω) ∧
      Surjective (e ∘ globalThetaToComponent F μ ω) ∧
      ∀ q, HasPositivePettisIntegral ν
        (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • globalThetaNormOneAction F k q)
        ↑(e (globalThetaToComponent F μ ω q)) := by
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  letI : T2Space (Θ F) := globalThetaQuotient_t2Space F
  obtain ⟨s, hs, hFix, hEig, hPettis⟩ := globalThetaComponent_pettisSection F μ ω ν
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    have hp := Measure.measure_pos_of_nonempty_interior (s := (univ : Set (K F))) ν (by simp)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)).ne'
  let e := ContinuousLinearMap.equivThetaCharacterSubspace (globalThetaNormOneAction F)
    (fun k ↦ (ω k : ℂ)) _ s hs hEig (fun q ↦ (hFix q).mpr) (Units.mk0 _ hmass)
  exact ⟨e, e.isOpenMap.comp (globalThetaToComponent_isOpenMap F μ ω),
    e.surjective.comp hs.surjective, hPettis⟩

/-- The isotypic section of the global homogeneous quotient map. -/
theorem globalThetaComponent_isotypicSection :
    ∃ s : (E F ⧸ M F μ ω) →L[ℂ] Θ F,
      LeftInverse (globalThetaToComponent F μ ω) s ∧
      (∀ q, s (globalThetaToComponent F μ ω q) = q ↔
        ∀ k, globalThetaNormOneAction F k q = (ω k : ℂ) • q) ∧
      (∀ q k, globalThetaNormOneAction F k (s q) = (ω k : ℂ) • s q) := by
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  obtain ⟨s, hs, hFix, hEig, _⟩ :=
    globalThetaComponent_pettisSection F μ ω (Measure.haar : Measure (K F))
  exact ⟨s, hs, hFix, hEig⟩

/-- Haar averaging gives a continuous section of the homogeneous quotient map. -/
theorem globalThetaComponent_section :
    ∃ s : (E F ⧸ M F μ ω) →L[ℂ] Θ F,
      ∀ q, globalThetaToComponent F μ ω (s q) = q := by
  obtain ⟨s, hs, _⟩ := globalThetaComponent_isotypicSection F μ ω
  exact ⟨s, hs⟩

/-- The homogeneous transpose on the quotient by the actual component kernel. -/
def globalHomogeneousThetaTranspose :
    StrongDual ℂ (E F ⧸ M F μ ω) →L[ℂ] StrongDual ℂ (E F) :=
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ (M F μ ω).mkQL

/-- Quotient Mellin evaluation of the homogeneous theta class. -/
def globalHomogeneousThetaLineEval (y : ℝ) : StrongDual ℂ (E F ⧸ M F μ ω) :=
  (M F μ ω).liftQL (globalThetaLineTestEval F μ ω y) fun f hf ↦
    (globalThetaComponent_ker F μ ω f).mp hf y

@[simp] theorem globalThetaTranspose_lineEval (y : ℝ) :
    globalThetaTranspose F (globalThetaLineEval F μ ω y) = globalThetaLineTestEval F μ ω y := rfl

@[simp] theorem globalHomogeneousThetaTranspose_lineEval (y : ℝ) :
    globalHomogeneousThetaTranspose F μ ω (globalHomogeneousThetaLineEval F μ ω y) =
      globalThetaLineTestEval F μ ω y := rfl

theorem globalHomogeneousThetaTranspose_isEmbedding :
    IsEmbedding (globalHomogeneousThetaTranspose F μ ω) := by
  apply quotientDual_strongEmbedding_of_bounded_lifts
  intro B hB
  obtain ⟨s, hs⟩ := globalThetaComponent_section F μ ω
  obtain ⟨C, hC, hCB⟩ := globalTheta_bounded_lift F (s '' B) (hB.image s)
  refine ⟨C, hC.isVonNBounded ℂ, ?_⟩
  intro q hq
  obtain ⟨f, hf, he⟩ := hCB (mem_image_of_mem s hq)
  exact ⟨f, hf, (congrArg (globalThetaToComponent F μ ω) he).trans (hs q)⟩

theorem globalHomogeneousThetaTranspose_covariant
    (T : StrongDual ℂ (E F ⧸ M F μ ω)) (k : K F) (g : Idele F) (hg : ideleClassMap F g = k.val)
    (f : E F) :
    globalHomogeneousThetaTranspose F μ ω T (GlobalBruhat.leftTranslate F g f) =
      (ω k : ℂ) * globalHomogeneousThetaTranspose F μ ω T f := by
  have he : (M F μ ω).mkQ (GlobalBruhat.leftTranslate F g f) =
      (ω k : ℂ) • (M F μ ω).mkQ f := by
    rw [← map_smul]
    change (Submodule.Quotient.mk _ : E F ⧸ M F μ ω) = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, globalThetaComponent_ker]
    intro y
    rw [map_sub, globalThetaLineTestEval_translate_normOne F μ ω y k g hg, map_smul, smul_eq_mul,
      sub_self]
  change T ((M F μ ω).mkQ (GlobalBruhat.leftTranslate F g f)) = (ω k : ℂ) * T ((M F μ ω).mkQ f)
  rw [he, map_smul, smul_eq_mul]

theorem globalThetaHomogeneousDistributions_isClosed :
    IsClosed {T : StrongDual ℂ (E F) | ∀ (k : K F) (g : Idele F), ideleClassMap F g = k.val →
      ∀ f, T (GlobalBruhat.leftTranslate F g f) = (ω k : ℂ) * T f} := by
  let G := {z : K F × Idele F | ideleClassMap F z.2 = z.1.val}
  rw [show {T : StrongDual ℂ (E F) | ∀ (k : K F) (g : Idele F), ideleClassMap F g = k.val →
      ∀ f, T (GlobalBruhat.leftTranslate F g f) = (ω k : ℂ) * T f} =
      ⋂ (z : G) (f : E F), {T : StrongDual ℂ (E F) |
        T (GlobalBruhat.leftTranslate F z.val.2 f) = (ω z.val.1 : ℂ) * T f} from by
          ext T
          simp [G]]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun f ↦
    isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const _))

/-- A single Mellin line generates the homogeneous transpose range for each character. -/
theorem globalHomogeneousThetaTranspose_range_line (d : ℝ → ℂ) (hd : ∀ y, d y ≠ 0) :
    range (globalHomogeneousThetaTranspose F μ ω) =
      closure (Submodule.span ℂ (range fun y : ℝ ↦ d y • globalThetaLineTestEval F μ ω y) :
        Set (StrongDual ℂ (E F))) := by
  let l (y : ℝ) := d y • globalThetaLineTestEval F μ ω y
  have hM (f : E F) : f ∈ M F μ ω ↔ ∀ y, l y f = 0 := by
    rw [globalThetaComponent_ker F μ ω f]
    constructor
    · intro h y
      change d y * globalThetaLineTestEval F μ ω y f = 0
      rw [h, mul_zero]
    · intro h y
      exact (mul_eq_zero.mp (h y)).resolve_left (hd y)
  change range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ (M F μ ω).mkQL) =
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ (E F)))
  rw [quotientDual_strongRange, globalThetaTest_span_eq F l (M F μ ω) hM]

end
end Masullo
