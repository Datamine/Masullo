import SLocalPrimaryPolarBlocks
import DyninMityagin

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

universe u

section Basis

variable {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]

/-- The three properties in Corollary 7.3.1.8 for a basis with its chosen
coordinate functionals. -/
def HasOrbitalBasisDuality (x : ℕ → X) (D : ℕ → StrongDual ℂ X) : Prop :=
  let V := strongDual_withBoundedSeminorms (E := X)
  letI : IsTopologicalAddGroup (StrongDual ℂ X) := V.topologicalAddGroup
  letI : ContinuousSMul ℂ (StrongDual ℂ X) := V.continuousSMul
  let G := fun n ↦ strongBidualEvaluation (x n)
  IsEquicontinuousBasis x D ∧ IsShrinking x D ∧ IsBoundedlyComplete x ∧
    IsEquicontinuousBasis D G ∧ IsShrinking D G ∧ IsBoundedlyComplete D

private theorem orbitalBasisDuality_of_nuclear [PolynormableSpace ℂ X] [T2Space X]
    [BarrelledSpace ℂ X]
    (hN : NuclearLocallyConvex.{u, u} X)
    (hC : @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X))
    (x : ℕ → X) (D : ℕ → StrongDual ℂ X)
    (hb : IsSchauderBasis x D) (ha : IsAbsolute x D) :
    HasOrbitalBasisDuality x D := by
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := hC
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear hN
  have hE : (e : X → StrongDual ℂ (StrongDual ℂ X)) = strongBidualEvaluation := by
    funext x
    exact ContinuousLinearMap.ext (he x)
  have hRef : IsHomeomorph (strongBidualEvaluation (E := X)) := hE ▸ e.toHomeomorph.isHomeomorph
  obtain ⟨hsh, hbc, _, hbd, hsd⟩ := absoluteBasis_duality hRef hb ha
  let V := strongDual_withBoundedSeminorms (E := X)
  letI : IsTopologicalAddGroup (StrongDual ℂ X) := V.topologicalAddGroup
  letI : ContinuousSMul ℂ (StrongDual ℂ X) := V.continuousSMul
  letI : PolynormableSpace ℂ (StrongDual ℂ X) := V.toPolynormableSpace
  letI : BarrelledSpace ℂ (StrongDual ℂ X) :=
    strongDual_barrelled_of_bidually_surjective hRef.surjective
  exact ⟨schauderBasis_equicontinuous_of_barrelled hb, hsh, hbc,
    schauderBasis_equicontinuous_of_barrelled hsh, hsd, hbd⟩

private theorem orbitalBasisDuality_of_unconditional [PolynormableSpace ℂ X] [T2Space X]
    [BarrelledSpace ℂ X]
    (hN : NuclearLocallyConvex.{u, u} X)
    (hC : @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X))
    {ι : Type*} [DecidableEq ι] (x : ι → X) (D : ι → StrongDual ℂ X)
    (horth : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hs : ∀ y : X, HasSum (fun i ↦ D i y • x i) y) (e : ℕ ≃ ι) :
    HasOrbitalBasisDuality (x ∘ e) (D ∘ e) := by
  have hb : IsSchauderBasis (x ∘ e) (D ∘ e) := by
    refine ⟨fun m n ↦ ?_, fun y ↦ ?_⟩
    · simpa only [Function.comp_apply, e.injective.eq_iff] using horth (e m) (e n)
    · exact Tendsto.mono_left (e.hasSum_iff.mpr (hs y)) (SummationFilter.conditional ℕ).le_atTop
  have ha := isAbsolute_of_isNuclearTVS hN hb (schauderBasis_equicontinuous_of_barrelled hb)
  exact orbitalBasisDuality_of_nuclear hN hC _ _ hb ha

end Basis

section Decompositions

variable {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]

def IsEquicontinuousDecomposition (P : ℕ → X →L[ℂ] X) : Prop :=
  letI := IsTopologicalAddGroup.rightUniformSpace X
  EquicontinuousAt (fun k ↦ ⇑(∑ n ∈ Finset.Iic k, P n)) 0

def IsBoundedlyCompleteDecomposition (P : ℕ → X →L[ℂ] X) : Prop :=
  ∀ a : ℕ → X, (∀ n, P n (a n) = a n) →
    IsVonNBounded ℂ (range fun k : ℕ ↦ ∑ n ∈ Finset.Iic k, a n) →
    Summable a (SummationFilter.conditional ℕ)

private theorem equicontinuousDecomposition_of_expansion [PolynormableSpace ℂ X]
    [BarrelledSpace ℂ X] (P : ℕ → X →L[ℂ] X)
    (h : ∀ x : X, HasSum (fun n ↦ P n x) x) :
    IsEquicontinuousDecomposition P := by
  letI := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let F (k : ℕ) : X →L[ℂ] X := ∑ n ∈ Finset.Iic k, P n
  have ht (x : X) : Tendsto (fun k ↦ F k x) atTop (𝓝 x) := by
    have hs : HasSum (fun n ↦ P n x) x (SummationFilter.conditional ℕ) :=
      Tendsto.mono_left (h x) (SummationFilter.conditional ℕ).le_atTop
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hs
    simpa only [F, Function.comp_def, ← Nat.range_succ_eq_Iic, sum_apply]
      using hs.comp (tendsto_add_atTop_nat 1)
  exact (PolynormableSpace.banach_steinhaus (𝓕 := F)
    (fun x ↦ (ht x).isVonNBounded_range ℂ)).equicontinuous 0

private theorem boundedlyCompleteDecomposition_of_compactClosure [T2Space X]
    (hcompact : ∀ B : Set X, IsVonNBounded ℂ B → IsCompact (closure B))
    (P : ℕ → X →L[ℂ] X)
    (hp : ∀ m n (x : X), P m (P n x) = if m = n then P n x else 0)
    (h : ∀ x : X, HasSum (fun n ↦ P n x) x) :
    IsBoundedlyCompleteDecomposition P := by
  intro a ha hb
  let s (k : ℕ) := ∑ n ∈ Finset.Iic k, a n
  have hfilter : Filter.map s atTop ≤ 𝓟 (closure (range s)) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Eventually.of_forall fun k ↦ subset_closure (mem_range_self k)
  obtain ⟨x, _, hx⟩ := (hcompact (range s) hb).exists_mapClusterPt hfilter
  have he (m : ℕ) : P m x = a m := by
    have hc := hx.continuousAt_comp (P m).continuous.continuousAt
    have hh : ∀ᶠ k : ℕ in atTop, P m (s k) = a m := by
      filter_upwards [eventually_ge_atTop m] with k hk
      have hs (n : ℕ) : P m (a n) = if m = n then a m else 0 := by
        have he := hp m n (a n)
        rw [ha n] at he
        by_cases hn : m = n
        · subst n
          simpa using he
        · simpa [hn] using he
      rw [show s k = ∑ n ∈ Finset.Iic k, a n from rfl, map_sum]
      simp [hs, hk]
    exact isClosed_singleton.mem_of_mapClusterPt hc hh
  have hu : HasSum a x := (h x).congr_fun fun n ↦ (he n).symm
  exact ⟨x, Tendsto.mono_left hu (SummationFilter.conditional ℕ).le_atTop⟩

private def poleProjectionTranspose (P : X →L[ℂ] X) : StrongDual ℂ X →L[ℂ] StrongDual ℂ X :=
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ P

/-- The basis properties for a sequence of finite pole projections.
Shrinking means the transposed projections expand the strong dual,
and their transposes expand the strong bidual. -/
def HasOrbitalDecompositionDuality (P : ℕ → X →L[ℂ] X) : Prop :=
  let V := strongDual_withBoundedSeminorms (E := X)
  letI : IsTopologicalAddGroup (StrongDual ℂ X) := V.topologicalAddGroup
  letI : ContinuousSMul ℂ (StrongDual ℂ X) := V.continuousSMul
  let T := fun n ↦ poleProjectionTranspose (P n)
  IsEquicontinuousDecomposition P ∧ IsBoundedlyCompleteDecomposition P ∧
    IsEquicontinuousDecomposition T ∧ IsBoundedlyCompleteDecomposition T ∧
    (∀ g : StrongDual ℂ X, HasSum (fun n ↦ T n g) g) ∧
    ∀ L : StrongDual ℂ (StrongDual ℂ X), HasSum (fun n ↦ poleProjectionTranspose (T n) L) L

private theorem orbitalDecompositionDuality_of_nuclear
    [PolynormableSpace ℂ X] [T2Space X] [BarrelledSpace ℂ X]
    (hN : NuclearLocallyConvex.{u,u} X)
    (hC : @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X))
    (hDN : NuclearLocallyConvex.{u,u} (StrongDual ℂ X))
    (hDC : CompleteSpace (StrongDual ℂ X))
    (P : ℕ → X →L[ℂ] X)
    (hp : ∀ m n (x : X), P m (P n x) = if m = n then P n x else 0)
    (h : ∀ x : X, HasSum (fun n ↦ P n x) x)
    (hD : ∀ g : StrongDual ℂ X, HasSum (fun n ↦ poleProjectionTranspose (P n) g) g) :
    HasOrbitalDecompositionDuality P := by
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := hC
  let V := strongDual_withBoundedSeminorms (E := X)
  let D := StrongDual ℂ X
  letI : IsTopologicalAddGroup D := V.topologicalAddGroup
  letI : ContinuousSMul ℂ D := V.continuousSMul
  letI : PolynormableSpace ℂ D := hDN.2.1
  letI : CompleteSpace D := hDC
  have hcompact (B : Set X) (hb : IsVonNBounded ℂ B) : IsCompact (closure B) :=
    (nuclearLocallyConvex_totallyBounded hN hb).closure.isCompact_of_isClosed isClosed_closure
  have hdcompact (B : Set D) (hb : IsVonNBounded ℂ B) : IsCompact (closure B) :=
    (nuclearLocallyConvex_totallyBounded hDN hb).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear hN
  have hE : (e : X → StrongDual ℂ D) = strongBidualEvaluation := by
    funext x
    exact ContinuousLinearMap.ext (he x)
  letI : BarrelledSpace ℂ D :=
    strongDual_barrelled_of_bidually_surjective (hE ▸ e.surjective)
  let T := fun n ↦ poleProjectionTranspose (P n)
  have ht (m n : ℕ) (g : D) : T m (T n g) = if m = n then T n g else 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change g (P n (P m x)) = _
    by_cases hmn : m = n
    · subst n
      simp [hp, T, poleProjectionTranspose]
    · simp [hp, hmn, Ne.symm hmn]
  refine ⟨equicontinuousDecomposition_of_expansion P h,
    boundedlyCompleteDecomposition_of_compactClosure hcompact P hp h,
    equicontinuousDecomposition_of_expansion T hD,
    boundedlyCompleteDecomposition_of_compactClosure hdcompact T ht hD, hD, ?_⟩
  intro L
  obtain ⟨y, rfl⟩ := e.surjective L
  refine (e.toContinuousLinearMap.hasSum (h y)).congr_fun fun n ↦ ?_
  apply ContinuousLinearMap.ext
  intro g
  change (e y) (T n g) = (e (P n y)) g
  exact (he y (T n g)).trans (he (P n y) g).symm

end Decompositions

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
  (hνG : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
  (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hνS : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F))
    Measure.count (sLocalClassHaar F S ν))

include hνG hνS in
/-- The actual primary orbital quotient is complete, nuclear and barrelled. -/
theorem sLocalPrimaryQuotient_structure
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    NuclearLocallyConvex.{u,u} X ∧
      @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X) ∧ BarrelledSpace ℂ X := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let M := sLocalHomogeneousThetaKernel F S ν A
  let Y := SLocalHomogeneousThetaQuotient F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := Y ⧸ R
  let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
  have hR : IsClosed (R : Set Y) :=
    sLocalFiniteNonzeroTestSubspace_map_isClosed F S (fun v ↦ μ v.val) ν hνS A W
  have hN := nuclearLocallyConvex_quotient (sLocalHomogeneousTheta_primalStructure F S ν A).1 R hR
  letI : BarrelledSpace ℂ Y := (sLocalHomogeneousTheta_barrelled F S ν A).1
  obtain ⟨L, hL⟩ := exists_sLocalPrimaryQuotient_testSection F S (μG := μ) (η := η)
    (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  exact ⟨hN, homogeneousSection_complete (sLocalBruhat_complete F S) Q L hL, quotient_barrelled R⟩

include hνG hνS in
/-- The continuous lifting identifies the strong dual with a complemented
subspace of the strong dual of the S-local test space. -/
theorem sLocalPrimaryQuotient_strongDual_structure
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    NuclearLocallyConvex.{u,u} (StrongDual ℂ X) ∧ CompleteSpace (StrongDual ℂ X) := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let M := sLocalHomogeneousThetaKernel F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
  let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
  obtain ⟨L, hL⟩ := exists_sLocalPrimaryQuotient_testSection F S (μG := μ) (η := η)
    (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  let D := StrongDual ℂ X
  let G := StrongDual ℂ (E F S)
  let j : D →L[ℂ] G := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ Q
  let r : G →L[ℂ] D := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ L
  have hj : LeftInverse r j := fun g ↦ ContinuousLinearMap.ext fun x ↦ congrArg g (hL x)
  have hEmb := hj.isEmbedding r.continuous j.continuous
  have hN := sLocalBruhat_strongDual_nuclear F S
  letI : CompleteSpace G := sLocalBruhat_strongDual_complete F S
  have hclosed : IsClosed (range j) := by
    rw [show range j = {g : G | j (r g) = g} by
      ext g
      change (∃ x : D, j x = g) ↔ j (r g) = g
      exact ⟨by rintro ⟨x,rfl⟩; rw [hj x], fun hg ↦ ⟨r g,hg⟩⟩]
    exact isClosed_eq (j.continuous.comp r.continuous) continuous_id
  refine ⟨nuclearLocallyConvex_of_embedding j hEmb hN, ?_⟩
  change CompleteSpace D
  have hjU : IsUniformInducing j := AddMonoidHom.isUniformInducing_of_isInducing
    (f := j.toLinearMap.toAddMonoidHom) hEmb.isInducing
  exact hjU.completeSpace hclosed.isComplete

include hνG hνS in
/-- The primal and strong-dual Fourier orbital bases have all three
properties in Corollary 7.3.1.8 for every enumeration. The same holds
for individual Laurent bases when the selected pole multiplicities
are at most one. -/
theorem sLocalPrimaryOrbitalDuality
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let J := SLocalPrimaryEulerJetIndex F S A p W
    let d := sLocalPrimaryEulerPeriod p
    let t := sLocalSelectedFinitePoleCount F S A W
    let l := sLocalPoleCount F S A
    let B (c : ℂ) := ↥(Finset.Ioc (l c - t c) (l c))
    let Z₀ (f : E F S) (z : ℂ) :=
      sLocalProductZetaContinued F S (fun v ↦ μ v.val) A⁻¹ (sLocalRealArchParameters F S A⁻¹)
        (sLocalComplexArchParameters F S A⁻¹) (sLocalFourierCompression F S f) (1-z)
    (∃ (x : J × ℤ → X) (D : J × ℤ → StrongDual ℂ X),
      (∀ i f, D i (R.mkQ (M.mkQ f)) = iteratedDeriv i.1.2.val (Z₀ f)
        (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)) ∧
      ∀ e : ℕ ≃ J × ℤ, HasOrbitalBasisDuality (x ∘ e) (D ∘ e)) ∧
    ((∀ c, t c ≤ 1) →
      ∃ (x : (Σ c : ℂ, B c) → X) (D : (Σ c : ℂ, B c) → StrongDual ℂ X),
        (∀ i f, D i (R.mkQ (M.mkQ f)) =
          sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f) ∧
        ∀ e : ℕ ≃ (Σ c : ℂ, B c), HasOrbitalBasisDuality (x ∘ e) (D ∘ e)) := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let M := sLocalHomogeneousThetaKernel F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
  obtain ⟨hN, hC, hB⟩ := sLocalPrimaryQuotient_structure F S μ η νG hνG ν hνS ω hs hu hp hW
  letI : PolynormableSpace ℂ X := hN.2.1
  letI : T2Space X := hN.1
  letI : BarrelledSpace ℂ X := hB
  constructor
  · obtain ⟨x, D, hval, horth, hsum, _, _, _⟩ :=
      exists_sLocalPrimaryQuotient_compressedFourier_bases F S (μG := μ) (η := η)
        (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
    exact ⟨x, D, hval, fun e ↦ orbitalBasisDuality_of_unconditional hN hC x D horth hsum e⟩
  · intro hsimple
    obtain ⟨x, D, hval, horth, hsum, _, _⟩ :=
      exists_sLocalPrimaryQuotient_polar_bases_of_simple_all_stages F S (μ := μ) (η := η)
        (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW hsimple
    exact ⟨x, D, hval, fun e ↦ orbitalBasisDuality_of_unconditional hN hC x D horth hsum e⟩

set_option maxHeartbeats 2000000 in
include hνG hνS in
/-- The grouped polar decomposition has the primal and dual properties in
Corollary 7.3.1.8 for every enumeration of the active pole centers. -/
theorem sLocalPrimaryPolarDecomposition_duality
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let t := sLocalSelectedFinitePoleCount F S A W
    let l := sLocalPoleCount F S A
    let B (c : ℂ) := ↥(Finset.Ioc (l c - t c) (l c))
    ∃ (x : (Σ c : ℂ, B c) → X) (D : (Σ c : ℂ, B c) → StrongDual ℂ X),
      (∀ i f, D i (R.mkQ (M.mkQ f)) =
        sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f) ∧
      (∀ i j, D i (x j) = if i = j then 1 else 0) ∧
      ∀ e : ℕ ≃ {c : ℂ // 0 < t c},
        HasOrbitalDecompositionDuality
          (fun n ↦ ∑ k : B (e n).val, (D ⟨(e n).val,k⟩).smulRight (x ⟨(e n).val,k⟩)) := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let M := sLocalHomogeneousThetaKernel F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
  let t := sLocalSelectedFinitePoleCount F S A W
  let l := sLocalPoleCount F S A
  let B (c : ℂ) := ↥(Finset.Ioc (l c - t c) (l c))
  let I := {c : ℂ // 0 < t c}
  obtain ⟨hN, hC, hBar⟩ := sLocalPrimaryQuotient_structure F S μ η νG hνG ν hνS ω hs hu hp hW
  obtain ⟨hDN, hDC⟩ := sLocalPrimaryQuotient_strongDual_structure F S μ η νG hνG ν hνS ω hs hu hp hW
  letI : PolynormableSpace ℂ X := hN.2.1
  letI : T2Space X := hN.1
  letI : BarrelledSpace ℂ X := hBar
  obtain ⟨x, D, hval, horth, hsum, _, hdual⟩ :=
    exists_sLocalPrimaryQuotient_polar_blocks_all_stages F S (μ := μ) (η := η)
      (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  let P (c : ℂ) : X →L[ℂ] X := ∑ k : B c, (D ⟨c,k⟩).smulRight (x ⟨c,k⟩)
  have he (c : ℂ) (y : X) : P c y = ∑ k : B c, D ⟨c,k⟩ y • x ⟨c,k⟩ := by
    simp [P]
  have hzero (c : ℂ) (hc : c ∉ range (Subtype.val : I → ℂ)) : P c = 0 := by
    have hn : t c = 0 := Nat.eq_zero_of_not_pos fun hh ↦ hc ⟨⟨c,hh⟩,rfl⟩
    letI : IsEmpty (B c) := ⟨fun k ↦ by
      have hk := Finset.mem_Ioc.mp k.property
      change l c - t c < k.val ∧ k.val ≤ l c at hk
      have hleft : l c = l c - t c := by rw [hn, Nat.sub_zero]
      exact (not_lt_of_ge hk.2) (hleft.trans_lt hk.1)⟩
    simp [P]
  have hproject (c z : ℂ) (y : X) :
      P c (P z y) = if c = z then P z y else 0 := by
    have hloc (k : B c) : D ⟨c,k⟩ (P z y) = if c = z then D ⟨c,k⟩ y else 0 := by
      rw [he]
      exact biorthogonal_block_sum_apply x D (fun i j ↦ by
        by_cases hij : i = j <;> simpa [hij] using horth i j) z ⟨c,k⟩ y
    rw [he c]
    simp_rw [hloc]
    by_cases hc : c = z
    · subst z
      simpa only [ite_true] using (he c y).symm
    · simp [hc]
  have ht (c : ℂ) (g : StrongDual ℂ X) :
      poleProjectionTranspose (P c) g = ∑ k : B c, g (x ⟨c,k⟩) • D ⟨c,k⟩ := by
    ext y
    change g (P c y) = _
    rw [he, map_sum]
    simp only [sum_apply, smul_apply, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
  refine ⟨x, D, hval, horth, fun e ↦ ?_⟩
  have hproj (m n : ℕ) (y : X) :
      P (e m).val (P (e n).val y) = if m = n then P (e n).val y else 0 := by
    have hc : ((e m).val = (e n).val) ↔ m = n :=
      ⟨fun h ↦ e.injective (Subtype.ext h), fun h ↦ congrArg (fun j ↦ (e j).val) h⟩
    simpa only [hc] using hproject (e m).val (e n).val y
  apply orbitalDecompositionDuality_of_nuclear hN hC hDN hDC (fun n ↦ P (e n).val) hproj
  · intro y
    have h := (hsum y).congr_fun fun c ↦ he c y
    have hs₀ := (Subtype.val_injective.hasSum_iff (g := (Subtype.val : I → ℂ))
      (fun c hc ↦ by rw [hzero c hc, zero_apply])).mpr h
    exact e.hasSum_iff.mpr hs₀
  · intro g
    have h := (hdual g).congr_fun fun c ↦ ht c g
    have hs₀ := (Subtype.val_injective.hasSum_iff (g := (Subtype.val : I → ℂ))
      (fun c hc ↦ by
        rw [hzero c hc]
        ext y
        change g ((0 : X →L[ℂ] X) y) = (0 : ℂ)
        simp)).mpr h
    exact e.hasSum_iff.mpr hs₀

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A nonempty set of active primary pole centers is countably infinite. -/
theorem sLocalPrimaryActivePoleCenters_enumerable_or_empty
    (θ : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let I := {c : ℂ // 0 < sLocalSelectedFinitePoleCount F S θ W c}
    Nonempty (ℕ ≃ I) ∨ IsEmpty I := by
  let t := sLocalSelectedFinitePoleCount F S θ W
  let I := {c : ℂ // 0 < t c}
  let C := sLocalPrimaryEulerCell F S θ p W
  let d := sLocalPrimaryEulerPeriod p
  let point (i : C × ℤ) := (((i.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)
  have ht (i : C × ℤ) : 0 < t (point i) := by
    have he : point i = (i.1.val : ℂ) * Complex.I + ((i.2 : ℝ) * d : ℝ) * Complex.I := by
      dsimp [point]
      push_cast
      ring
    have hp₀ := (mem_sLocalPrimaryEulerCell_iff F S θ hp hW _).mp i.1.property
    have hperiod := (sLocalPrimaryEulerProduct_periodic F S θ hp hW
      ((i.1.val : ℂ) * Complex.I) i.2).2
    change t ((i.1.val : ℂ) * Complex.I + ((i.2 : ℝ) * d : ℝ) * Complex.I) =
      t ((i.1.val : ℂ) * Complex.I) at hperiod
    rw [he, hperiod]
    exact hp₀.2
  let f (i : C × ℤ) : I := ⟨point i, ht i⟩
  have hinj : Injective f := by
    rintro ⟨x,m⟩ ⟨y,n⟩ h
    have he : x.val + (m : ℝ) * d = y.val + (n : ℝ) * d := by
      simpa [f, point, Complex.mul_im] using congrArg (fun i : I ↦ i.val.im) h
    obtain ⟨hx, hm⟩ := sLocalPrimaryEulerCell_representation_unique F S θ hp x.property y.property m n he
    exact Prod.ext (Subtype.ext hx) hm
  have hsurj : Surjective f := by
    intro c
    obtain ⟨x,hx,m,hc,_⟩ := sLocalPrimaryEulerCell_represents F S θ hp hW c.property
    exact ⟨(⟨x,hx⟩,m), Subtype.ext hc.symm⟩
  let e : C × ℤ ≃ I := Equiv.ofBijective f ⟨hinj,hsurj⟩
  rcases isEmpty_or_nonempty C with hc | hc
  · letI : IsEmpty C := hc
    exact Or.inr (Function.isEmpty e.symm)
  · obtain ⟨x⟩ := hc
    obtain ⟨g, hg⟩ := Countable.exists_injective_nat (C × ℤ)
    let b : ℕ ↪ C × ℤ := ⟨fun n ↦ (x,(n : ℤ)), fun _ _ h ↦ Int.ofNat_inj.mp (congrArg Prod.snd h)⟩
    obtain ⟨q⟩ := b.antisymm ⟨g,hg⟩
    exact Or.inl ⟨q.trans e⟩

include hνG hνS in
/-- Corrected Corollary 7.3.1.8 for the primary systems of corrected
Theorem 7.3.1.6, with complete Laurent blocks at repeated poles. -/
theorem sLocalPrimaryOrbitalDuality_corrected
    [Subsingleton (SPicardGroup F S)] (θ : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) :
    let W := sLocalPrimaryPlaces F S p
    let M := sLocalHomogeneousThetaKernel F S ν θ
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν θ) ⧸ R
    let J := SLocalPrimaryEulerJetIndex F S θ p W
    let d := sLocalPrimaryEulerPeriod p
    let t := sLocalSelectedFinitePoleCount F S θ W
    let l := sLocalPoleCount F S θ
    let B (c : ℂ) := ↥(Finset.Ioc (l c - t c) (l c))
    let Z₀ (f : E F S) (z : ℂ) :=
      sLocalProductZetaContinued F S (fun v ↦ μ v.val) θ⁻¹ (sLocalRealArchParameters F S θ⁻¹)
        (sLocalComplexArchParameters F S θ⁻¹) (sLocalFourierCompression F S f) (1-z)
    (∃ (x : J × ℤ → X) (D : J × ℤ → StrongDual ℂ X),
      (∀ i f, D i (R.mkQ (M.mkQ f)) = iteratedDeriv i.1.2.val (Z₀ f)
        (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)) ∧
      ∀ e : ℕ ≃ J × ℤ, HasOrbitalBasisDuality (x ∘ e) (D ∘ e)) ∧
    (∃ (x : (Σ c : ℂ, B c) → X) (D : (Σ c : ℂ, B c) → StrongDual ℂ X),
      (∀ i f, D i (R.mkQ (M.mkQ f)) =
        sLocalLaurentCoeff F S (fun v ↦ μ v.val) θ i.1 i.2.val f) ∧
      (∀ i j, D i (x j) = if i = j then 1 else 0) ∧
      ∀ e : ℕ ≃ {c : ℂ // 0 < t c},
        HasOrbitalDecompositionDuality
          (fun n ↦ ∑ k : B (e n).val, (D ⟨(e n).val,k⟩).smulRight (x ⟨(e n).val,k⟩))) ∧
    ((∀ c, t c ≤ 1) →
      ∃ (x : (Σ c : ℂ, B c) → X) (D : (Σ c : ℂ, B c) → StrongDual ℂ X),
        (∀ i f, D i (R.mkQ (M.mkQ f)) =
          sLocalLaurentCoeff F S (fun v ↦ μ v.val) θ i.1 i.2.val f) ∧
        ∀ e : ℕ ≃ (Σ c : ℂ, B c), HasOrbitalBasisDuality (x ∘ e) (D ∘ e)) := by
  have hs := sIdeleClassInclusion_surjective_of_trivial_picard F S
  obtain ⟨ω, hu, hθ⟩ := exists_unramified_globalNormOne_for_local F S θ hs
  subst θ
  have hW : sLocalPrimaryPlaces F S p ⊆ sLocalPrimaryPlaces F S p := Finset.Subset.refl _
  obtain ⟨hF, hL⟩ := sLocalPrimaryOrbitalDuality F S
    (μ := μ) (η := η) (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  exact ⟨hF, sLocalPrimaryPolarDecomposition_duality F S
    (μ := μ) (η := η) (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW, hL⟩

end

end Masullo
