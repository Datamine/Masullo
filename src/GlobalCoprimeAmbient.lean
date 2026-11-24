import GlobalCoprimality
import BergmanDifference
import ModulatedCyclicComparison
import IdelicStageCofinalBasis
import IdelicMellinSummation
import ModulatedPettisConvolution
import BergmanVerticalTranslation

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 3000000

private abbrev E := PositiveRealExponentialDecay (univ : Set ℝ)
private theorem hU : (univ : Set ℝ).Nonempty := ⟨0, mem_univ _⟩

/-- The entire logarithmic Mellin transform diagonalizes the actual finite
product of cyclic differences, retaining repeated factors. -/
theorem entireLogMellin_cyclicDifferenceProduct_apply (gs : List (ℝ × Circle))
    (f : E) (z : ℂ) :
    (entireLogMellin (logDecayCyclicDifferenceProduct univ hU gs f)).val z =
      (gs.map fun g ↦ 1 - (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z))).prod *
        (entireLogMellin f).val z := by
  have h (g : ℝ × Circle) (u : E) :
      (entireLogMellin (logDecayCyclicDifference univ hU g u)).val z =
        (1 - (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z))) * (entireLogMellin u).val z := by
    change (entireLogMellin (u - (g.2 : ℂ) • exponentialSchwartzTranslation g.1 u)).val z = _
    rw [map_sub, map_smul]
    change (entireLogMellin u).val z -
      (g.2 : ℂ) * (entireLogMellin (exponentialSchwartzTranslation g.1 u)).val z = _
    rw [entireMellin_translation]
    ring
  induction gs with
  | nil => simp [logDecayCyclicDifferenceProduct]
  | cons g gs ih =>
    change (entireLogMellin (logDecayCyclicDifference univ hU g
      (logDecayCyclicDifferenceProduct univ hU gs f))).val z = _
    rw [h, ih, List.map_cons, List.prod_cons, mul_assoc]

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev B := SchwartzBergman (univ : Set ℝ)
private abbrev m := mellinClassModulus F
private abbrev τ : Multiplicative ℝ →ₜ* IdeleClass F :=
  ⟨ideleClassExpSection F, ideleClassExpSection_continuous F⟩

private theorem hτ (t : Multiplicative ℝ) : m F (τ F t) = t :=
  ideleClassLogNorm_expSection F t

local instance : CompactSpace (K F) := normOneIdeleClass_compact F
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

private theorem hm : IsProperMap (m F) :=
  isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap

private theorem hK : (m F).toMonoidHom.ker = K F :=
  ideleClassLogNorm_ker_eq_normOne F

private def logKernelInclusion : (m F).toMonoidHom.ker →ₜ* K F where
  toFun k := ⟨k.val, hK F ▸ k.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable (ω : PontryaginDual (K F))

private def w : PontryaginDual (m F).toMonoidHom.ker :=
  ContinuousMonoidHom.comp ω (logKernelInclusion F)
private abbrev ξ := normOneEulerCharacter F ω
private abbrev P := finiteHeckeOmissionMultiplier F (ξ F ω)

private theorem extendedLogKernelCharacter (g : IdeleClass F) :
    extendModulatedCharacter (G := IdeleClass F) (m F) (τ F) (hτ F) (w F ω) g = ξ F ω g := by
  rfl

/-- The actual entire exponential-decay isotype on the idele-class group. -/
abbrev GlobalCoprimeDecay :=
  @modulatedDecayIsotype (IdeleClass F) inferInstance inferInstance inferInstance
    ideleClasses_hausdorff ideleClasses_locallyCompact (m F) (w F ω) (univ : Set ℝ)

local instance : IsTopologicalAddGroup
    (@ModulatedExponentialInductive (IdeleClass F) inferInstance inferInstance inferInstance
      ideleClasses_hausdorff ideleClasses_locallyCompact (m F) (univ : Set ℝ)) :=
  (PolynormableSpace.withSeminorms ℂ _).topologicalAddGroup

/-- The actual product of unramified uniformizer differences. -/
def globalCoprimeDifference (W : Finset (Place F))
    (π : ∀ v : Place F, (v.adicCompletion F)ˣ) :
    GlobalCoprimeDecay F ω →L[ℂ] GlobalCoprimeDecay F ω :=
  @modulatedDecayIsotypeDifferenceProduct (IdeleClass F) inferInstance inferInstance inferInstance
    ideleClasses_hausdorff ideleClasses_locallyCompact (m F) (τ F) (hτ F) (w F ω) (hm F) univ hU
    ((W.filter (unramifiedFiniteCharacter F (ξ F ω))).toList.map
      fun v ↦ (ideleClassMap F (singleFiniteIdele F v (π v)))⁻¹)

private theorem globalCoprimeDifference_factor
    (π : ∀ v : Place F, (v.adicCompletion F)ˣ) (v : Place F)
    (hπ : Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hv : unramifiedFiniteCharacter F (ξ F ω) v) (z : ℂ) :
    let g := (ideleClassMap F (singleFiniteIdele F v (π v)))⁻¹
    1 - (((extendModulatedCharacter (G := IdeleClass F) (m F) (τ F) (hτ F) (w F ω) g)⁻¹ : Circle) : ℂ) *
        Complex.exp (-(((m F g).toAdd : ℂ) * z)) = P F ω {v} z := by
  dsimp only
  rw [extendedLogKernelCharacter, map_inv, inv_inv]
  have heuler := euler_singleton_exp F (ξ F ω) v z
  change P F ω {v} z = _ at heuler
  rw [heuler]
  have hn : (m F ((ideleClassMap F (singleFiniteIdele F v (π v)))⁻¹)).toAdd =
      Real.log (v.asIdeal.absNorm : ℝ) := by
    rw [map_inv]
    change -(Real.log (ideleClassNorm F (ideleClassMap F (singleFiniteIdele F v (π v))))) = _
    rw [ideleClassNorm_mk, singleFiniteIdele_norm, norm_finiteUniformizer F v _ hπ,
      Real.log_inv, neg_neg]
  rw [hn, neg_mul]
  have hc : heckeEulerCoefficient F (ξ F ω) (chosenFiniteUniformizer F) v =
      (ξ F ω (ideleClassMap F (singleFiniteIdele F v (π v))) : ℂ) := by
    unfold heckeEulerCoefficient
    rw [ite_eq_left hv]
    exact congrArg (fun u : Circle ↦ (u : ℂ))
      (unramifiedFiniteCharacter_uniformizer_eq F (ξ F ω) v hv (π v)
        (chosenFiniteUniformizer F v) hπ (chosenFiniteUniformizer_spec F v)).symm
  exact congrArg (fun a : ℂ ↦ 1 - a * Complex.exp (-((Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * z)))
    hc.symm

private theorem globalCoprimeDifference_prod (W : Finset (Place F))
    (π : ∀ v : Place F, (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ W, Valued.v.IsUniformizer (π v : v.adicCompletion F)) (z : ℂ) :
    let T := W.filter (unramifiedFiniteCharacter F (ξ F ω))
    let gs := T.toList.map fun v ↦ (ideleClassMap F (singleFiniteIdele F v (π v)))⁻¹
    ((gs.map fun g ↦ ((m F g).toAdd,
      (extendModulatedCharacter (G := IdeleClass F) (m F) (τ F) (hτ F) (w F ω) g)⁻¹)).map fun g ↦
      1 - (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z))).prod = P F ω W z := by
  intro T gs
  dsimp only [gs]
  rw [List.map_map, List.map_map]
  rw [Finset.prod_map_toList]
  calc
    _ = ∏ v ∈ T, P F ω {v} z := by
      apply Finset.prod_congr rfl
      intro v hv
      exact globalCoprimeDifference_factor F ω π v (hπ v (Finset.mem_filter.mp hv).1)
        (Finset.mem_filter.mp hv).2 z
    _ = P F ω W z := by
      simp only [P, finiteHeckeOmissionMultiplier, Finset.prod_singleton]
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro v hv hnot
      have hram : ¬unramifiedFiniteCharacter F (ξ F ω) v :=
        fun h ↦ hnot (Finset.mem_filter.mpr ⟨hv, h⟩)
      simp [heckeEulerCoefficient, hram]

/-- Mellin coordinates intertwine the native idele-class difference product
with multiplication by the reciprocal Euler divisor. -/
theorem exists_globalCoprime_ambientMellin (W : Finset (Place F))
    (π : ∀ v : Place F, (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ W, Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    ∃ J : GlobalCoprimeDecay F ω ≃L[ℂ] B,
      (∀ b g, (J.symm b).val.val g =
        (entireLogMellin.symm b).val (m F g).toAdd * (((ξ F ω g)⁻¹ : Circle) : ℂ)) ∧
      ∀ u, J (globalCoprimeDifference F ω W π u) =
        finiteHeckeOmissionBergmanMul F (ξ F ω) W (J u) := by
  obtain ⟨e, he, _, h⟩ := @exists_modulatedDecayRadialDifferenceModel (IdeleClass F)
    inferInstance inferInstance inferInstance ideleClasses_hausdorff ideleClasses_locallyCompact
    (ideleClass_secondCountable F) (m F) (τ F) (hτ F) (w F ω) (hm F) univ hU
  refine ⟨e.symm.trans entireLogMellin, ?_, ?_⟩
  · intro b g
    change (e (entireLogMellin.symm b)).val.val g = _
    rw [he, extendedLogKernelCharacter]
  · intro u
    obtain ⟨f, rfl⟩ := e.surjective u
    apply Subtype.ext
    funext z
    dsimp only [globalCoprimeDifference]
    rw [h]
    simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
      finiteHeckeOmissionBergmanMul_apply, entireLogMellin_cyclicDifferenceProduct_apply]
    rw [globalCoprimeDifference_prod F ω W π hπ]

private theorem omissionMul_range (W : Finset (Place F)) :
    (finiteHeckeOmissionBergmanMul F (ξ F ω) W).range =
      bergmanDivisorSubmodule (P F ω W) := by
  ext b
  have hc : Differentiable ℂ (fun _ : ℂ ↦ (1 : ℂ)) := differentiable_const _
  have htop (a : B) : a ∈ bergmanDivisorSubmodule (fun _ : ℂ ↦ 1) := by
    have ha : Differentiable ℂ a.val := by
      simpa only [preimage_univ, differentiableOn_univ] using a.property.2.1
    exact (bergmanDivisorSubmodule_mem_iff hc a).mpr ⟨a.val, ha, fun z ↦ (one_mul _).symm⟩
  change (∃ a : B, finiteHeckeOmissionBergmanMul F (ξ F ω) W a = b) ↔ _
  simpa only [htop, true_and, mul_one] using
    finiteHeckeOmissionBergmanMul_divisor_range F (ξ F ω) W hc b

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev Test := (GlobalBruhat.polarEvaluation F).ker
private abbrev X := (Test F).map (globalIdelicZetaComponentKernel F η ω).mkQ

include hν in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem globalPolarFreeMellin_inverse_apply (f : Test F) (t : ℝ) :
    (entireLogMellin.symm
      (globalPolarFreeMellin F ν η hν ω (globalPolarFreeTestClass F η ω f))).val t =
      adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val
        (τ F (Multiplicative.ofAdd t)) := by
  have hv : GlobalBruhat.polarEvaluation F f.val = 0 := f.property
  have hp : globalZetaPolarVanishes F f.val (compactIdeleClassCharacter F ω) :=
    (globalZetaPolarVanishes_compact_iff F f.val ω).mpr
      (Or.inr ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩)
  let b := globalPoleFreeRadialProfile F ν ω f.val hp
  have hb : entireLogMellin b =
      globalPolarFreeMellin F ν η hν ω (globalPolarFreeTestClass F η ω f) := by
    apply Subtype.ext
    rw [globalPolarFreeMellin_val]
    change (entireLogMellin b).val = globalQuotientMellinFunction F ν η hν ω
      ((globalIdelicZetaComponentKernel F η ω).mkQ f.val)
    rw [globalQuotientMellinFunction_mk]
    exact globalPoleFreeRadialProfile_mellin F ν ω f.val hp
  rw [← hb, entireLogMellin.symm_apply_apply]
  rfl

include hν in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem globalThetaMellinEmbedding_apply
    (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
    (hJ : ∀ b g, (J.symm b).val.val g =
      (entireLogMellin.symm b).val (m F g).toAdd * (((ξ F ω g)⁻¹ : Circle) : ℂ))
    (f : Test F) (g : IdeleClass F) :
    (J.symm (globalPolarFreeMellin F ν η hν ω (globalPolarFreeTestClass F η ω f))).val.val g =
      adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val g := by
  rw [hJ, globalPolarFreeMellin_inverse_apply F ω ν η hν]
  let k := ideleClassNormOnePart F g
  have hg : k.val * τ F (m F g) = g := div_mul_cancel (a := g) _
  have htheta := adelicHomogeneousTheta_translate F ν ω
    (GlobalBruhat.algebraicEquiv F f.val).val k (τ F (m F g))
  rw [hg] at htheta
  rw [htheta, mul_comm]
  rfl

include μ hν in
/-- Corrected Theorem 7.5.0.1. Homogeneous theta induces the topological
isomorphism on the actual principal-value and idele-class difference
quotients. At ramified places the principal-value factor is the identity,
so the ambient difference product uses the unramified selected places. -/
theorem exists_globalCoprime_thetaQuotient (W : Finset (Place F))
    (π : ∀ v : Place F, (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ W, Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    let N := (globalPolarFreePrincipalValues F ν η μ hν ω W).toLinearMap.range
    let D := (globalCoprimeDifference F ω W π).range
    ∃ (j : X F ω η →L[ℂ] GlobalCoprimeDecay F ω)
      (q : (X F ω η ⧸ N) ≃L[ℂ] (GlobalCoprimeDecay F ω ⧸ D)),
      IsClosedEmbedding j ∧
      (∀ f : Test F, ∀ g,
        (j (globalPolarFreeTestClass F η ω f)).val.val g =
          adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val g) ∧
      ∀ x, q (N.mkQ x) = D.mkQ (j x) := by
  intro N D
  obtain ⟨J, hJ, hT⟩ := exists_globalCoprime_ambientMellin F ω W π hπ
  let j := J.symm.toContinuousLinearMap.comp (globalPolarFreeMellin F ν η hν ω)
  obtain ⟨p, hp⟩ := exists_globalCoprime_mellinQuotient F ν η μ hν ω W
  let M := finiteHeckeOmissionBergmanMul F (ξ F ω) W
  let Q : (GlobalCoprimeDecay F ω ⧸ D) ≃L[ℂ] (B ⧸ M.range) :=
    quotientIntertwiningEquiv J _ M (fun u ↦ (hT u).symm)
  let e : (GlobalCoprimeDecay F ω ⧸ D) ≃L[ℂ] (B ⧸ bergmanDivisorSubmodule (P F ω W)) :=
    omissionMul_range F ω W ▸ Q
  have he (u : GlobalCoprimeDecay F ω) :
      e (D.mkQ u) = (bergmanDivisorSubmodule (P F ω W)).mkQ (J u) := by
    dsimp only [e]
    generalize omissionMul_range F ω W = h
    change (h ▸ Q) (D.mkQ u) = _
    have hQ : Q (D.mkQ u) = M.range.mkQ (J u) := rfl
    revert h
    generalize bergmanDivisorSubmodule (P F ω W) = S
    intro h
    cases h
    exact hQ
  refine ⟨j, p.trans e.symm, ?_, ?_, ?_⟩
  · obtain ⟨r, hr, hmin, _⟩ := exists_globalHeckeDivisor_coprime_ideals F ν η μ hν ω W
    obtain ⟨k, hk⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r
      (globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin)
    have hc := bergmanDivisorSubmodule_isClosed
      (fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt)
    have hEmb : IsClosedEmbedding (globalPolarFreeMellin F ν η hν ω) := by
      have hEq : (globalPolarFreeMellin F ν η hν ω : X F ω η → B) =
          Subtype.val ∘ k := (funext hk).symm
      rw [hEq]
      exact hc.isClosedEmbedding_subtypeVal.comp k.toHomeomorph.isClosedEmbedding
    exact J.symm.toHomeomorph.isClosedEmbedding.comp hEmb
  · exact globalThetaMellinEmbedding_apply F ω ν η hν J hJ
  · intro x
    change e.symm (p (N.mkQ x)) = D.mkQ (j x)
    apply e.injective
    rw [e.apply_symm_apply, hp, he]
    congr 1
    exact (J.apply_symm_apply _).symm

/-- The ambient Mellin chart transports quotients by a closed theta image
when that image has a continuous linear divisor model. -/
private theorem nativeThetaDivisorQuotient {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (D : Submodule ℂ B) (hc : IsClosed (D : Set B))
    (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
    (L : Y →L[ℂ] B) (k : Y ≃L[ℂ] D) (hk : ∀ x, (k x).val = L x) :
    let j := J.symm.toContinuousLinearMap.comp L
    ∃ q : (GlobalCoprimeDecay F ω ⧸ j.toLinearMap.range) ≃L[ℂ] (B ⧸ D),
      IsClosedEmbedding j ∧
      ∀ u, q (j.toLinearMap.range.mkQ u) = D.mkQ (J u) := by
  intro j
  let R := j.toLinearMap.range
  have hEq : (j : Y → GlobalCoprimeDecay F ω) = J.symm ∘ Subtype.val ∘ k := by
    funext x
    exact congrArg J.symm (hk x).symm
  have hEmb : IsClosedEmbedding j := by
    rw [hEq]
    exact J.symm.toHomeomorph.isClosedEmbedding.comp
      (hc.isClosedEmbedding_subtypeVal.comp k.toHomeomorph.isClosedEmbedding)
  have hR (u : GlobalCoprimeDecay F ω) : u ∈ R ↔ J u ∈ D := by
    constructor
    · rintro ⟨x, rfl⟩
      change J (j x) ∈ D
      rw [hEq]
      change J (J.symm (k x).val) ∈ D
      rw [J.apply_symm_apply]
      exact (k x).property
    · intro hu
      obtain ⟨x, hx⟩ := k.surjective (⟨J u, hu⟩ : D)
      refine ⟨x, ?_⟩
      change j x = u
      rw [hEq, Function.comp_apply, Function.comp_apply, hx, J.symm_apply_apply]
  let T := R.liftQL (D.mkQL.comp J.toContinuousLinearMap) (by
    intro u hu
    exact (Submodule.Quotient.mk_eq_zero D).mpr ((hR u).mp hu))
  let U := D.liftQL (R.mkQL.comp J.symm.toContinuousLinearMap) (by
    intro b hb
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    apply (hR (J.symm b)).mpr
    rwa [J.apply_symm_apply])
  let q := ContinuousLinearEquiv.equivOfInverse T U
    (by
      intro x
      obtain ⟨u, rfl⟩ := R.mkQ_surjective x
      change R.mkQ (J.symm (J u)) = R.mkQ u
      rw [J.symm_apply_apply])
    (by
      intro x
      obtain ⟨b, rfl⟩ := D.mkQ_surjective x
      change D.mkQ (J (J.symm b)) = D.mkQ b
      rw [J.apply_symm_apply])
  exact ⟨q, hEmb, fun _ ↦ rfl⟩

include μ hν in
/-- The quotient of the native decay isotype by the actual homogeneous
theta image is modeled by the entire Bergman quotient by the cleared Hecke
divisor. The model preserves the ambient Mellin coordinates. -/
theorem exists_globalSpectral_thetaMellinQuotient (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt
      (globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0) z ≤
      meromorphicOrderAt (globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0) z) :
    let D := bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r)
    ∃ (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
      (j : X F ω η →L[ℂ] GlobalCoprimeDecay F ω)
      (q : (GlobalCoprimeDecay F ω ⧸ j.toLinearMap.range) ≃L[ℂ] (B ⧸ D)),
      IsClosedEmbedding j ∧
      (∀ f : Test F, ∀ g, (j (globalPolarFreeTestClass F η ω f)).val.val g =
        adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val g) ∧
      (∀ b g, (J.symm b).val.val g =
        (entireLogMellin.symm b).val (m F g).toAdd * (((ξ F ω g)⁻¹ : Circle) : ℂ)) ∧
      ∀ u, q (j.toLinearMap.range.mkQ u) = D.mkQ (J u) := by
  intro D
  obtain ⟨J, hJ, _⟩ := exists_globalCoprime_ambientMellin F ω ∅ (chosenFiniteUniformizer F)
    (fun _ h ↦ (Finset.notMem_empty _ h).elim)
  let L := globalPolarFreeMellin F ν η hν ω
  let j := J.symm.toContinuousLinearMap.comp L
  obtain ⟨k, hk⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r
    (globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin)
  have hc : IsClosed (D : Set B) := bergmanDivisorSubmodule_isClosed
    (fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt)
  obtain ⟨q, hEmb, hq⟩ := nativeThetaDivisorQuotient F ω D hc J L k hk
  exact ⟨J, j, q, hEmb, globalThetaMellinEmbedding_apply F ω ν η hν J hJ, hJ, hq⟩

include μ hν in
/-- The quotient by the actual polar-free principal-value theta image is
the Bergman quotient by the cleared Hecke divisor times the selected
reciprocal Euler product. -/
theorem exists_globalOrbital_thetaMellinQuotient (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt
      (globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0) z ≤
      meromorphicOrderAt (globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0) z)
    (W : Finset (Place F)) :
    let D := bergmanDivisorSubmodule (fun z ↦ P F ω W z * globalHeckeClearedZeta F ν ω r z)
    ∃ (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
      (j : X F ω η →L[ℂ] GlobalCoprimeDecay F ω)
      (q : (GlobalCoprimeDecay F ω ⧸ j.toLinearMap.range) ≃L[ℂ] (B ⧸ D)),
      IsClosedEmbedding j ∧
      (∀ f : Test F, ∀ g, (j (globalPolarFreeTestClass F η ω f)).val.val g =
        adelicHomogeneousTheta F ν ω
          (GlobalBruhat.algebraicEquiv F (globalWeilPrincipalValues F W f.val)).val g) ∧
      ∀ u, q (j.toLinearMap.range.mkQ u) = D.mkQ (J u) := by
  intro D
  obtain ⟨J, hJ, _⟩ := exists_globalCoprime_ambientMellin F ω W (chosenFiniteUniformizer F)
    (fun v _ ↦ chosenFiniteUniformizer_spec F v)
  let V := globalPolarFreePrincipalValues F ν η μ hν ω W
  let L := (globalPolarFreeMellin F ν η hν ω).comp V
  let j := J.symm.toContinuousLinearMap.comp L
  obtain ⟨k, hk⟩ := exists_globalPV_polarFree_equiv_of_min F ν η μ hν ω r hr hmin W
  have hX (f : Test F) :
      V (globalPolarFreeTestClass F η ω f) =
        globalPolarFreeTestClass F η ω
          ⟨globalWeilPrincipalValues F W f.val, globalPV_polarEvaluation_eq_zero F ν η μ hν W f.val f.property⟩ := by
    apply Subtype.ext
    exact globalHomogeneousPrincipalValues_mk F ν η μ hν ω W f.val
  have hL (x : X F ω η) : (k x).val = L x := by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    let f₀ : Test F := ⟨f, hf⟩
    have he : x = globalPolarFreeTestClass F η ω f₀ := Subtype.ext hfx.symm
    subst x
    apply Subtype.ext
    funext z
    rw [hk]
    change _ = (globalPolarFreeMellin F ν η hν ω (V (globalPolarFreeTestClass F η ω f₀))).val z
    rw [hX, globalPolarFreeMellin_val]
    exact congrFun (globalQuotientMellinFunction_mk F ν η hν ω (globalWeilPrincipalValues F W f)) z |>.symm
  have hP : Differentiable ℂ (P F ω W) := fun z ↦
    (finiteHeckeOmissionMultiplier_analytic F (ξ F ω) W z).differentiableAt
  have hG : Differentiable ℂ (globalHeckeClearedZeta F ν ω r) := fun z ↦
    (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  obtain ⟨q, he, hq⟩ := nativeThetaDivisorQuotient F ω D
    (bergmanDivisorSubmodule_isClosed (hP.mul hG)) J L k hL
  refine ⟨J, j, q, he, ?_, hq⟩
  intro f g
  change (J.symm (globalPolarFreeMellin F ν η hν ω (V (globalPolarFreeTestClass F η ω f)))).val.val g = _
  rw [hX]
  exact globalThetaMellinEmbedding_apply F ω ν η hν J hJ _ g

section CompactConvolution

local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

private abbrev AmbientDecay :=
  @ModulatedExponentialInductive (IdeleClass F) inferInstance inferInstance inferInstance
    ideleClasses_hausdorff ideleClasses_locallyCompact (m F) (univ : Set ℝ)

variable (σ : Measure (IdeleClass F)) [σ.IsHaarMeasure]

/-- Mellin multiplier of the actual compact-test convolution. -/
def globalDecayConvolutionMultiplier (φ : BruhatCompactTest (IdeleClass F)) (z : ℂ) : ℂ :=
  ∫ g, φ.val.val g * ((ξ F ω g : Circle) : ℂ) *
    Complex.exp (((m F g).toAdd : ℂ) * z) ∂σ

/-- The compact-test Pettis convolution preserves the native decay isotype
and acts there by the holomorphic Mellin multiplier. -/
theorem exists_globalDecay_mellinConvolution :
    ∃ (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
      (A : BruhatCompactTest (IdeleClass F) → GlobalCoprimeDecay F ω →L[ℂ] GlobalCoprimeDecay F ω),
      (∀ b g, (J.symm b).val.val g =
        (entireLogMellin.symm b).val (m F g).toAdd * (((ξ F ω g)⁻¹ : Circle) : ℂ)) ∧
      (∀ φ u, HasPositivePettisIntegral σ
        (fun g ↦ φ.val.val g • ModulatedExponentialInductive.translate (m F) univ g u.val)
        (A φ u).val) ∧
      (∀ φ u z, (J (A φ u)).val z =
        globalDecayConvolutionMultiplier F ω σ φ z * (J u).val z) ∧
      ∀ φ, Differentiable ℂ (globalDecayConvolutionMultiplier F ω σ φ) := by
  classical
  let D := AmbientDecay F
  let H := GlobalCoprimeDecay F ω
  let tr : IdeleClass F → D →ₗ[ℂ] D :=
    @ModulatedExponentialInductive.translate (IdeleClass F) inferInstance inferInstance inferInstance
      ideleClasses_hausdorff ideleClasses_locallyCompact (m F) univ
  obtain ⟨J, hJ, _⟩ := exists_globalCoprime_ambientMellin F ω ∅ (chosenFiniteUniformizer F)
    (fun v hv ↦ (Finset.notMem_empty v hv).elim)
  obtain ⟨A₀, hA₀⟩ := @exists_modulatedDecayPettisConvolution (IdeleClass F)
    inferInstance inferInstance inferInstance ideleClasses_hausdorff ideleClasses_locallyCompact
    inferInstance inferInstance σ inferInstance (m F) univ hU (hm F) (fun t ↦ ⟨τ F t, hτ F t⟩)
  have htr (g : IdeleClass F) (u : H) : tr g u.val ∈ H := by
    intro k x
    change u.val.val (g⁻¹ * ((k.val)⁻¹ * x)) = (w F ω k : ℂ) * u.val.val (g⁻¹ * x)
    rw [← mul_assoc, mul_comm g⁻¹ _, mul_assoc]
    exact u.property k (g⁻¹ * x)
  have hav (φ : BruhatCompactTest (IdeleClass F)) (u : H) (x : IdeleClass F) :
      (A₀ φ u.val).val x = ∫ g, φ.val.val g * u.val.val (g⁻¹ * x) ∂σ := by
    have h := hA₀ φ u.val (@ModulatedExponentialInductive.evaluation (IdeleClass F)
      inferInstance inferInstance inferInstance ideleClasses_hausdorff ideleClasses_locallyCompact
      (m F) univ hU x)
    simpa [Function.comp_def, map_smul, smul_eq_mul, ModulatedExponentialInductive.evaluation] using h.2
  have hpres (φ : BruhatCompactTest (IdeleClass F)) (u : H) : A₀ φ u.val ∈ H := by
    intro k x
    rw [hav, hav, ← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro g
    change φ.val.val g * (tr g u.val).val ((k.val)⁻¹ * x) =
      (w F ω k : ℂ) * (φ.val.val g * (tr g u.val).val x)
    have he : (tr g u.val).val ((k.val)⁻¹ * x) =
        (w F ω k : ℂ) * (tr g u.val).val x := htr g u k x
    rw [he]
    ring
  let A (φ : BruhatCompactTest (IdeleClass F)) : H →L[ℂ] H :=
    ((A₀ φ).comp H.subtypeL).codRestrict H (hpres φ)
  have hTr (g : IdeleClass F) (u : H) (z : ℂ) :
      (J (⟨tr g u.val, htr g u⟩ : H)).val z =
        (ξ F ω g : ℂ) * Complex.exp (((m F g).toAdd : ℂ) * z) * (J u).val z := by
    let f := entireLogMellin.symm (J u)
    let b := entireLogMellin (((ξ F ω g : Circle) : ℂ) •
      exponentialSchwartzTranslation (-(m F g).toAdd) f)
    have huv (x : IdeleClass F) :
        u.val.val x = f.val (m F x).toAdd * (((ξ F ω x)⁻¹ : Circle) : ℂ) := by
      have he := hJ (J u) x
      rw [J.symm_apply_apply] at he
      exact he
    have hEq : (⟨tr g u.val, htr g u⟩ : H) = J.symm b := by
      apply Subtype.ext
      apply ModulatedExponentialInductive.algebraicEquiv.injective
      apply Subtype.ext
      funext x
      change u.val.val (g⁻¹ * x) = (J.symm b).val.val x
      rw [huv, hJ, map_mul (m F), map_inv (m F), map_mul (ξ F ω), map_inv (ξ F ω),
        mul_inv_rev, inv_inv, Circle.coe_mul]
      have hf := entireLogMellin.symm_apply_apply
        (((ξ F ω g : Circle) : ℂ) • exponentialSchwartzTranslation (-(m F g).toAdd) f)
      change (entireLogMellin.symm b) = _ at hf
      rw [hf]
      change f.val (-(m F g).toAdd + (m F x).toAdd) * _ =
        ((ξ F ω g : Circle) : ℂ) * f.val ((m F x).toAdd + -(m F g).toAdd) * _
      rw [add_comm (-(m F g).toAdd)]
      ring
    rw [hEq, J.apply_symm_apply]
    change (entireLogMellin (((ξ F ω g : Circle) : ℂ) •
      exponentialSchwartzTranslation (-(m F g).toAdd) f)).val z = _
    rw [map_smul]
    change ((ξ F ω g : Circle) : ℂ) *
      (entireLogMellin (exponentialSchwartzTranslation (-(m F g).toAdd) f)).val z = _
    rw [entireMellin_translation, Complex.ofReal_neg, neg_mul, neg_neg,
      show entireLogMellin f = J u from entireLogMellin.apply_symm_apply (J u), mul_assoc]
  have hAct (φ : BruhatCompactTest (IdeleClass F)) (u : H) (z : ℂ) :
      (J (A φ u)).val z = globalDecayConvolutionMultiplier F ω σ φ z * (J u).val z := by
    let e : H →L[ℂ] ℂ := (bergmanNormalizedJet z 0).comp J.toContinuousLinearMap
    have hE (u' : H) : e u' = (J u').val z := by
      change bergmanNormalizedJet z 0 (J u') = _
      simp [bergmanNormalizedJet_apply]
    obtain ⟨ℓ, hℓ⟩ := StrongDual.exists_extension H e
    have hleft : ℓ (A₀ φ u.val) = (J (A φ u)).val z := (hℓ (A φ u)).trans (hE _)
    rw [← hleft]
    rw [show ℓ (A₀ φ u.val) = ∫ g, ℓ (φ.val.val g • tr g u.val) ∂σ from (hA₀ φ u.val ℓ).2]
    unfold globalDecayConvolutionMultiplier
    rw [← integral_mul_const]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro g
    change ℓ (φ.val.val g • tr g u.val) =
      φ.val.val g * ((ξ F ω g : Circle) : ℂ) *
        Complex.exp (((m F g).toAdd : ℂ) * z) * (J u).val z
    rw [map_smul, smul_eq_mul, show ℓ (tr g u.val) = (J (⟨tr g u.val, htr g u⟩ : H)).val z
      from (hℓ ⟨tr g u.val, htr g u⟩).trans (hE _), hTr]
    ring
  refine ⟨J, A, hJ, fun φ u ↦ hA₀ φ u.val, hAct, fun φ ↦ ?_⟩
  let b : B := ⟨fun z ↦ Complex.exp (z ^ 2), by
    simpa only [Set.preimage_univ, Set.indicator_univ] using
      gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ⟩
  let u := J.symm b
  have ha : Differentiable ℂ (J (A φ u)).val := by
    simpa only [preimage_univ, differentiableOn_univ] using (J (A φ u)).property.2.1
  have he : globalDecayConvolutionMultiplier F ω σ φ =
      fun z ↦ (J (A φ u)).val z * Complex.exp (-(z ^ 2)) := by
    funext z
    rw [hAct, show J u = b from J.apply_symm_apply b]
    change _ = (_ * Complex.exp (z ^ 2)) * Complex.exp (-(z ^ 2))
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [he]
  exact ha.mul (by fun_prop)

#print axioms exists_globalDecay_mellinConvolution

private theorem divisor_preimage_mapsTo (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
    (A : GlobalCoprimeDecay F ω →L[ℂ] GlobalCoprimeDecay F ω)
    (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hA : ∀ u z, (J (A u)).val z = p z * (J u).val z) :
    let R := (bergmanDivisorSubmodule g).comap J.toLinearMap
    Set.MapsTo A R R := by
  intro R
  intro u hu
  change J u ∈ bergmanDivisorSubmodule g at hu
  obtain ⟨q, hq, he⟩ := (bergmanDivisorSubmodule_mem_iff hg (J u)).mp hu
  change J (A u) ∈ bergmanDivisorSubmodule g
  exact (bergmanDivisorSubmodule_mem_iff hg _).mpr
    ⟨fun z ↦ p z * q z, hp.mul hq, fun z ↦ by rw [hA, he]; ring⟩

include μ hν in
/-- Theorem 7.4.1.1(1). The actual norm-weighted polar-free homogeneous theta
image is closed and preserved by compact-test Haar convolution. -/
theorem exists_globalShiftedTheta_closedInvariant (a : ℝ) :
    ∃ (j : X F ω η →L[ℂ] GlobalCoprimeDecay F ω)
      (A : BruhatCompactTest (IdeleClass F) → GlobalCoprimeDecay F ω →L[ℂ] GlobalCoprimeDecay F ω),
      let R := j.toLinearMap.range
      IsClosed (R : Set (GlobalCoprimeDecay F ω)) ∧
      (∀ f : Test F, ∀ q : IdeleClass F,
        (j (globalPolarFreeTestClass F η ω f)).val.val q =
          (((ideleClassNorm F q) ^ a : ℝ) : ℂ) *
            adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q) ∧
      (∀ φ, Set.MapsTo (A φ) R R) ∧
      ∀ φ u, HasPositivePettisIntegral σ
        (fun g ↦ φ.val.val g • ModulatedExponentialInductive.translate (m F) univ g u.val) (A φ u).val := by
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  obtain ⟨J, A, hJ, hPettis, hA, hdiff⟩ := exists_globalDecay_mellinConvolution F ω σ
  let G := globalHeckeClearedZeta F ν ω r
  let S := schwartzBergmanEntireShift (a : ℂ)
  let L := globalPolarFreeMellin F ν η hν ω
  let j := J.symm.toContinuousLinearMap.comp (S.toContinuousLinearMap.comp L)
  let D := bergmanDivisorSubmodule (fun z ↦ G (z + (a : ℂ)))
  have hG : Differentiable ℂ G := fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  have hD : Differentiable ℂ (fun z ↦ G (z + (a : ℂ))) := hG.comp (differentiable_id.add_const _)
  obtain ⟨k, hk⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r
    (globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin)
  have hR : j.toLinearMap.range = D.comap J.toLinearMap := by
    ext u
    change (∃ x, j x = u) ↔ J u ∈ D
    constructor
    · rintro ⟨x, rfl⟩
      change J (J.symm (S (L x))) ∈ D
      rw [J.apply_symm_apply]
      exact (bergmanDivisorSubmodule_shift_mem_iff hG (a : ℂ) (L x)).mpr
        ((hk x) ▸ (k x).property)
    · intro hu
      have hLu : S.symm (J u) ∈ bergmanDivisorSubmodule G := by
        apply (bergmanDivisorSubmodule_shift_mem_iff hG (a : ℂ) _).mp
        change S (S.symm (J u)) ∈ D
        rwa [S.apply_symm_apply]
      obtain ⟨x, hx⟩ := k.surjective (⟨_, hLu⟩ : bergmanDivisorSubmodule G)
      refine ⟨x, ?_⟩
      have hv : L x = S.symm (J u) := (hk x).symm.trans (congrArg Subtype.val hx)
      change J.symm (S (L x)) = u
      rw [hv, S.apply_symm_apply, J.symm_apply_apply]
  have hInvariant (φ : BruhatCompactTest (IdeleClass F)) :=
    divisor_preimage_mapsTo F ω _ hD J (A φ) _ (hdiff φ) (hA φ)
  have hClosed : IsClosed (j.toLinearMap.range : Set (GlobalCoprimeDecay F ω)) := by
    rw [hR]
    exact (bergmanDivisorSubmodule_isClosed hD).preimage J.continuous
  have hMaps (φ : BruhatCompactTest (IdeleClass F)) :
      Set.MapsTo (A φ) j.toLinearMap.range j.toLinearMap.range := by
    rw [hR]
    exact hInvariant φ
  refine ⟨j, A, hClosed, ?_, hMaps, hPettis⟩
  intro f q
  let x := globalPolarFreeTestClass F η ω f
  have hExp : Complex.exp ((a : ℂ) * ((m F q).toAdd : ℂ)) =
      (((ideleClassNorm F q) ^ a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Real.rpow_def_of_pos (ideleClassNorm_pos F q)]
    change (↑(Real.exp (a * Real.log (ideleClassNorm F q))) : ℂ) = _
    rw [mul_comm a]
  change (J.symm (S (L x))).val.val q = _
  rw [hJ, show (entireLogMellin.symm (S (L x))).val (m F q).toAdd =
      Complex.exp ((a : ℂ) * ((m F q).toAdd : ℂ)) * (entireLogMellin.symm (L x)).val (m F q).toAdd
      from schwartzBergmanEntireShift_inverse_profile (a : ℂ) (L x) (m F q).toAdd,
    hExp, mul_assoc, ← hJ (L x) q]
  exact congrArg (_ * ·) (globalThetaMellinEmbedding_apply F ω ν η hν J hJ f q)

#print axioms exists_globalShiftedTheta_closedInvariant

/-- The actual compact-test action descends to the spectral quotient that
retains the first `N` Taylor coordinates at each zero of the divisor. -/
theorem exists_globalDecay_truncatedConvolution (g : ℂ → ℂ) (N : ℕ) :
    ∃ (J : GlobalCoprimeDecay F ω ≃L[ℂ] B)
      (A : BruhatCompactTest (IdeleClass F) → GlobalCoprimeDecay F ω →L[ℂ] GlobalCoprimeDecay F ω),
      let W := bergmanTruncatedDivisorSubmodule g N
      (∀ b q, (J.symm b).val.val q =
        (entireLogMellin.symm b).val (m F q).toAdd * (((ξ F ω q)⁻¹ : Circle) : ℂ)) ∧
      (∀ φ u, HasPositivePettisIntegral σ
        (fun x ↦ φ.val.val x • ModulatedExponentialInductive.translate (m F) univ x u.val)
        (A φ u).val) ∧
      ∀ φ, ∃ T : (B ⧸ W) →L[ℂ] (B ⧸ W),
        ∀ u, T (W.mkQ (J u)) = W.mkQ (J (A φ u)) := by
  obtain ⟨J, A, hJ, hPettis, hA, hdiff⟩ := exists_globalDecay_mellinConvolution F ω σ
  refine ⟨J, A, hJ, hPettis, fun φ ↦ ?_⟩
  let M := J.toContinuousLinearMap.comp ((A φ).comp J.symm.toContinuousLinearMap)
  have hM (b : B) (z : ℂ) :
      (M b).val z = globalDecayConvolutionMultiplier F ω σ φ z * b.val z := by
    change (J (A φ (J.symm b))).val z = _
    rw [hA, J.apply_symm_apply]
  obtain ⟨T, hT⟩ := bergmanTruncatedDivisor_lift g N M _ (hdiff φ) hM
  refine ⟨T, fun u ↦ ?_⟩
  rw [hT]
  change (bergmanTruncatedDivisorSubmodule g N).mkQ (J (A φ (J.symm (J u)))) =
    (bergmanTruncatedDivisorSubmodule g N).mkQ (J (A φ u))
  rw [J.symm_apply_apply]

#print axioms exists_globalDecay_truncatedConvolution

include μ hν in
/-- Theorem 7.4.2.1(1). The principal-value subspace in the polar-free
homogeneous theta space is closed and invariant under actual Haar convolution.
The theorem also provides the induced continuous operator on its quotient. -/
theorem exists_globalFiniteOrbital_convolution (W : Finset (Place F)) :
    let N := (globalPolarFreePrincipalValues F ν η μ hν ω W).toLinearMap.range
    ∃ (j : X F ω η →L[ℂ] GlobalCoprimeDecay F ω)
      (A : BruhatCompactTest (IdeleClass F) → X F ω η →L[ℂ] X F ω η),
      IsClosed (N : Set (X F ω η)) ∧
      (∀ f : Test F, ∀ q : IdeleClass F,
        (j (globalPolarFreeTestClass F η ω f)).val.val q =
          adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q) ∧
      (∀ φ x, HasPositivePettisIntegral σ
        (fun g ↦ φ.val.val g • ModulatedExponentialInductive.translate (m F) univ g (j x).val)
        (j (A φ x)).val) ∧
      (∀ φ x z, (globalPolarFreeMellin F ν η hν ω (A φ x)).val z =
        globalDecayConvolutionMultiplier F ω σ φ z * (globalPolarFreeMellin F ν η hν ω x).val z) ∧
      (∀ φ, Set.MapsTo (A φ) N N) ∧
      ∀ φ, ∃ T : (X F ω η ⧸ N) →L[ℂ] (X F ω η ⧸ N), ∀ x, T (N.mkQ x) = N.mkQ (A φ x) := by
  intro N
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  obtain ⟨J, M, hJ, hPettis, hM, hdiff⟩ := exists_globalDecay_mellinConvolution F ω σ
  obtain ⟨q, hq⟩ := exists_globalCoprime_mellinQuotient F ν η μ hν ω W
  let L := globalPolarFreeMellin F ν η hν ω
  let j := J.symm.toContinuousLinearMap.comp L
  let G := globalHeckeClearedZeta F ν ω r
  let D := bergmanDivisorSubmodule G
  let E := bergmanDivisorSubmodule (P F ω W)
  have hG : Differentiable ℂ G := fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  have hP : Differentiable ℂ (P F ω W) := fun z ↦
    (finiteHeckeOmissionMultiplier_analytic F (ξ F ω) W z).differentiableAt
  obtain ⟨k, hk⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r
    (globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin)
  have hinD (x : X F ω η) : j x ∈ D.comap J.toLinearMap := by
    change J (J.symm (L x)) ∈ D
    rw [J.apply_symm_apply, ← hk x]
    exact (k x).property
  let A (φ : BruhatCompactTest (IdeleClass F)) : X F ω η →L[ℂ] X F ω η :=
    k.symm.toContinuousLinearMap.comp
      ((J.toContinuousLinearMap.comp ((M φ).comp j)).codRestrict D fun x ↦
        divisor_preimage_mapsTo F ω G hG J (M φ) _ (hdiff φ) (hM φ) (hinD x))
  have hAct (φ : BruhatCompactTest (IdeleClass F)) (x : X F ω η) :
      L (A φ x) = J (M φ (j x)) := by
    rw [← hk (A φ x)]
    exact congrArg Subtype.val (k.apply_symm_apply _)
  have hjA (φ : BruhatCompactTest (IdeleClass F)) (x : X F ω η) :
      j (A φ x) = M φ (j x) := by
    change J.symm (L (A φ x)) = _
    rw [hAct, J.symm_apply_apply]
  have hN (x : X F ω η) : x ∈ N ↔ L x ∈ E := by
    rw [← Submodule.Quotient.mk_eq_zero N, ← Submodule.Quotient.mk_eq_zero E]
    change N.mkQ x = 0 ↔ E.mkQ (L x) = 0
    rw [← hq x]
    exact ⟨fun h ↦ h ▸ q.map_zero,
      fun h ↦ q.injective (h.trans q.map_zero.symm)⟩
  have hClosed : IsClosed (N : Set (X F ω η)) := by
    rw [show (N : Set (X F ω η)) = L ⁻¹' E from Set.ext hN]
    exact (bergmanDivisorSubmodule_isClosed hP).preimage L.continuous
  have hMaps (φ : BruhatCompactTest (IdeleClass F)) : Set.MapsTo (A φ) N N := by
    intro x hx
    apply (hN (A φ x)).mpr
    rw [hAct]
    apply divisor_preimage_mapsTo F ω _ hP J (M φ) _ (hdiff φ) (hM φ)
    change J (J.symm (L x)) ∈ E
    rw [J.apply_symm_apply]
    exact (hN x).mp hx
  refine ⟨j, A, hClosed, globalThetaMellinEmbedding_apply F ω ν η hν J hJ,
    fun φ x ↦ ?_, fun φ x z ↦ ?_, hMaps, fun φ ↦ ?_⟩
  · rw [hjA]
    exact hPettis φ (j x)
  · change (L (A φ x)).val z = _
    rw [hAct, hM]
    change _ * (J (J.symm (L x))).val z = _
    rw [J.apply_symm_apply]
  · have hker : N ≤ (N.mkQL.comp (A φ)).ker := by
      intro x hx
      change A φ x ∈ N.mkQ.ker
      rw [N.ker_mkQ]
      exact hMaps φ hx
    exact ⟨N.liftQL (N.mkQL.comp (A φ)) hker, fun _ ↦ rfl⟩

#print axioms exists_globalFiniteOrbital_convolution

end CompactConvolution

#print axioms entireLogMellin_cyclicDifferenceProduct_apply
#print axioms exists_globalCoprime_ambientMellin
#print axioms exists_globalCoprime_thetaQuotient
#print axioms exists_globalSpectral_thetaMellinQuotient
#print axioms exists_globalOrbital_thetaMellinQuotient

end

end Masullo
