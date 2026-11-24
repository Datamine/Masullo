import SLocalZetaProduct
import SLocalEulerPoles
import SLocalMeromorphicKernels

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Local (v : Place F) := locallyConstantTests (v.adicCompletion F)
private abbrev X (S : Finset (Place F)) := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S

variable {S T : Finset (Place F)} (hST : S ⊆ T)

private def embedPlace : S → {v : T // v.val ∈ S} :=
  fun v ↦ ⟨⟨v.val, hST v.property⟩, v.property⟩

private def equivOldPlaces : S ≃ {v : T // v.val ∈ S} where
  toFun := embedPlace F hST
  invFun v := ⟨v.val.val, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def paddedFactor (g : ∀ v : S, Local F v.val) (v : T) : Local F v.val :=
  if h : v.val ∈ S then g ⟨v.val, h⟩ else finiteCompletionIntegerRingTest F v.val

include hST in
private theorem sLocalFiniteExtend_piProduct (g : ∀ v : S, Local F v.val) :
    sLocalFiniteExtend F S T (locallyConstantTestPiProduct g) =
      locallyConstantTestPiProduct (paddedFactor F (T := T) g) := by
  apply Subtype.ext
  funext x
  rw [sLocalFiniteExtend_apply F hST, locallyConstantTestPiProduct_apply,
    locallyConstantTestPiProduct_apply, ← Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S)]
  congr 1
  · apply Fintype.prod_equiv (equivOldPlaces F hST)
    intro v
    change (g v).val (x ⟨v.val, hST v.property⟩) =
      (paddedFactor F g ⟨v.val, hST v.property⟩).val (x ⟨v.val, hST v.property⟩)
    simp only [paddedFactor, dite_eq_left v.property]
  · have he (v : {v : T // v.val ∉ S}) :
        (paddedFactor F g v.val).val (x v.val) =
          if x v.val ∈ v.val.val.adicCompletionIntegers F then 1 else 0 := by
      rw [paddedFactor, dite_eq_right v.property]
      rfl
    simp_rw [he, Fintype.prod_boole]
    congr 1
    apply propext
    constructor
    · exact fun h v ↦ h v.val v.property
    · exact fun h v hv ↦ h ⟨v, hv⟩

variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]

private abbrev phase (S : Finset (Place F)) := ∀ v : S, (v.val.adicCompletion F)ˣ →ₜ* Circle

variable (χ : phase F S) (ψ : phase F T)
variable (hχ : ∀ v : S, ψ ⟨v.val, hST v.property⟩ = χ v)
variable (hu : ∀ v : T, v.val ∉ S → finiteZetaUnramified F v.val (ψ v))

/-- The scalar from multiplicative Haar integration of the inserted
integer rings at new unramified places. -/
def sLocalMellinPaddingHaarMass (S T : Finset (Place F)) : ℂ :=
  ∏ v : {v : T // v.val ∉ S}, (μ v.val.val).real (finitePlaceIntegralUnits F v.val.val)

/-- The new Euler denominators introduced by finite padding. -/
def sLocalMellinPaddingDenominator (S : Finset (Place F)) (ψ : phase F T) (z : ℂ) : ℂ :=
  ∏ v : {v : T // v.val ∉ S}, finiteZetaDenominator F v.val.val (ψ v.val) z

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ] in
include hχ hu in
private theorem sLocalFiniteZetaDenominator_pad (z : ℂ) :
    sLocalFiniteZetaDenominator F T ψ z =
      sLocalFiniteZetaDenominator F S χ z * sLocalMellinPaddingDenominator F S ψ z := by
  unfold sLocalFiniteZetaDenominator sLocalMellinPaddingDenominator
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S)]
  congr 1
  · symm
    apply Fintype.prod_equiv (equivOldPlaces F hST)
    intro v
    change _ = if finiteZetaUnramified F v.val (ψ ⟨v.val, hST v.property⟩) then
        finiteZetaDenominator F v.val (ψ ⟨v.val, hST v.property⟩) z else 1
    rw [hχ v]
  · apply Finset.prod_congr rfl
    intro v _
    rw [ite_eq_left (hu v.val v.property)]

include hχ hu in
private theorem sLocalFiniteZetaCleared_pad_piProduct (g : ∀ v : S, Local F v.val) (z : ℂ) :
    sLocalFiniteZetaCleared F T (fun v ↦ μ v.val) ψ z
      (sLocalFiniteExtend F S T (locallyConstantTestPiProduct g)) =
      sLocalFiniteZetaCleared F S (fun v ↦ μ v.val) χ z (locallyConstantTestPiProduct g) *
        sLocalMellinPaddingHaarMass F μ S T := by
  rw [sLocalFiniteExtend_piProduct F hST, sLocalFiniteZetaCleared_piProduct,
    sLocalFiniteZetaCleared_piProduct, ← Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S)]
  congr 1
  · symm
    apply Fintype.prod_equiv (equivOldPlaces F hST)
    intro v
    change finiteProductClearedLocal F S (fun u ↦ μ u.val) χ v (g v) z =
      finiteProductClearedLocal F T (fun u ↦ μ u.val) ψ ⟨v.val, hST v.property⟩
        (paddedFactor F g ⟨v.val, hST v.property⟩) z
    simp only [finiteProductClearedLocal, paddedFactor, dite_eq_left v.property, hχ v]
  · unfold sLocalMellinPaddingHaarMass
    apply Finset.prod_congr rfl
    intro v _
    simp only [finiteProductClearedLocal, paddedFactor, dite_eq_right v.property,
      ite_eq_left (hu v.val v.property)]
    exact finiteZetaClearedDistribution_integerRing_unramified F v.val.val (μ v.val.val) _
      (hu v.val v.property) z

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ] in
include hST in
private theorem sLocalFiniteExtend_add (f g : X F S) :
    sLocalFiniteExtend F S T (f + g) = sLocalFiniteExtend F S T f + sLocalFiniteExtend F S T g := by
  apply Subtype.ext
  funext x
  simp only [sLocalFiniteExtend_apply F hST, Submodule.coe_add, Pi.add_apply, add_mul]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ] in
include hST in
private theorem sLocalFiniteExtend_smul (c : ℂ) (f : X F S) :
    sLocalFiniteExtend F S T (c • f) = c • sLocalFiniteExtend F S T f := by
  apply Subtype.ext
  funext x
  simp only [sLocalFiniteExtend_apply F hST, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

include hχ hu in
/-- The pole-cleared finite Mellin transform of a padded test is multiplied
by the product of the Haar masses at the new places. -/
theorem sLocalFiniteZetaCleared_pad (f : X F S) (z : ℂ) :
    sLocalFiniteZetaCleared F T (fun v ↦ μ v.val) ψ z (sLocalFiniteExtend F S T f) =
      sLocalFiniteZetaCleared F S (fun v ↦ μ v.val) χ z f * sLocalMellinPaddingHaarMass F μ S T := by
  have hf : f ∈ Submodule.span ℂ (range (locallyConstantTestPiProduct
      (X := fun v : S ↦ v.val.adicCompletion F))) := by
    rw [locallyConstantTest_span_piProduct]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact sLocalFiniteZetaCleared_pad_piProduct F hST μ χ ψ hχ hu g z
  | zero =>
    have hzero : sLocalFiniteExtend F S T 0 = 0 := by
      have h := sLocalFiniteExtend_smul F hST 0 (0 : X F S)
      simpa only [zero_smul] using h
    rw [hzero, map_zero, map_zero, zero_mul]
  | add f g _ _ hf hg =>
    rw [sLocalFiniteExtend_add F hST, map_add, map_add, hf, hg, add_mul]
  | smul c f _ hf =>
    rw [sLocalFiniteExtend_smul F hST, map_smul, map_smul, hf, smul_eq_mul, smul_eq_mul, mul_assoc]

include hχ hu in
/-- Multiplying by the product of the new denominators cancels finite
padding wherever that product is nonzero. -/
theorem sLocalFiniteZetaContinued_pad_mul (f : X F S) (z : ℂ)
    (hz : sLocalMellinPaddingDenominator F S ψ z ≠ 0) :
    sLocalMellinPaddingDenominator F S ψ z *
      sLocalFiniteZetaContinued F T (fun v ↦ μ v.val) ψ z (sLocalFiniteExtend F S T f) =
      sLocalMellinPaddingHaarMass F μ S T * sLocalFiniteZetaContinued F S (fun v ↦ μ v.val) χ z f := by
  simp only [sLocalFiniteZetaContinued, smul_apply, smul_eq_mul,
    sLocalFiniteZetaDenominator_pad F hST χ ψ hχ hu,
    sLocalFiniteZetaCleared_pad F hST μ χ ψ hχ hu, mul_inv]
  let D := sLocalMellinPaddingDenominator F S ψ z
  let H := sLocalMellinPaddingHaarMass F μ S T
  let A := (sLocalFiniteZetaDenominator F S χ z)⁻¹
  let B := sLocalFiniteZetaCleared F S (fun v ↦ μ v.val) χ z f
  change D * (A * D⁻¹ * (B * H)) = H * (A * B)
  calc
    _ = (D * D⁻¹) * (H * (A * B)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hz, one_mul]

/-- Count the local Euler factors of the padding denominator which vanish. -/
def sLocalMellinPaddingPoleCount (S : Finset (Place F)) (ψ : phase F T) (c : ℂ) : ℕ :=
  (Finset.univ.filter fun v : {v : T // v.val ∉ S} ↦
    finiteZetaDenominator F v.val.val (ψ v.val) c = 0).card

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ] [∀ v : Place F, SigmaFinite (μ v)] in
theorem sLocalMellinPaddingHaarMass_ne_zero :
    sLocalMellinPaddingHaarMass F μ S T ≠ 0 := by
  unfold sLocalMellinPaddingHaarMass
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val.val (μ v.val.val)).ne'

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ] in
/-- The order of the padding denominator adds the multiplicities of all
new places, even when their poles share the same ordinate. -/
theorem sLocalMellinPaddingDenominator_order (c : ℂ) :
    meromorphicOrderAt (sLocalMellinPaddingDenominator F S ψ) c =
      (sLocalMellinPaddingPoleCount F S ψ c : WithTop ℤ) := by
  let D (v : {v : T // v.val ∉ S}) := finiteZetaDenominator F v.val.val (ψ v.val)
  have hD (v : {v : T // v.val ∉ S}) := finiteZetaDenominator_analytic F v.val.val (ψ v.val) c
  have hA : AnalyticAt ℂ (sLocalMellinPaddingDenominator F S ψ) c :=
    Finset.analyticAt_fun_prod _ fun v _ ↦ hD v
  obtain ⟨V, hV, hVn, he, _⟩ := analytic_finset_prod_factor_simpleZeros Finset.univ D c
    (fun v _ ↦ hD v) (fun v _ ↦ finiteZetaDenominator_simple_zero F v.val.val (ψ v.val) c)
  rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_natCast.mpr ⟨V, hV, hVn, he⟩,
    ENat.map_natCast]
  rfl

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ] in
private theorem sLocalMellinPaddingDenominator_eventually_ne_zero (c : ℂ) :
    ∀ᶠ z in 𝓝[≠] c, sLocalMellinPaddingDenominator F S ψ z ≠ 0 := by
  have hA : AnalyticAt ℂ (sLocalMellinPaddingDenominator F S ψ) c :=
    Finset.analyticAt_fun_prod _ fun v _ ↦ finiteZetaDenominator_analytic F v.val.val (ψ v.val) c
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hA.meromorphicAt).mp
  rw [sLocalMellinPaddingDenominator_order]
  exact WithTop.natCast_ne_top _

section Joint

variable (ωS : PontryaginDual (SLocalThetaNormOne F S))
  (ωT : PontryaginDual (SLocalThetaNormOne F T))
variable (hPhase : ∀ v : S, sLocalFiniteZetaPhases F T ωT ⟨v.val, hST v.property⟩ =
  sLocalFiniteZetaPhases F S ωS v)
variable (hNew : ∀ v : T, v.val ∉ S → finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F T ωT v))

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ] in
include hPhase hNew in
/-- The finite pole count changes by the order of the padding denominator. -/
theorem sLocalFinitePoleCount_pad (c : ℂ) :
    (sLocalFinitePolesAt F T ωT c).card =
      (sLocalFinitePolesAt F S ωS c).card +
        sLocalMellinPaddingPoleCount F S (sLocalFiniteZetaPhases F T ωT) c := by
  let D (U : Finset (Place F)) (τ : PontryaginDual (SLocalThetaNormOne F U)) (v : U) : ℂ :=
    if finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F U τ v) then
      finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F U τ v) c else 1
  let N (v : {v : T // v.val ∉ S}) :=
    finiteZetaDenominator F v.val.val (sLocalFiniteZetaPhases F T ωT v.val) c
  change (Finset.univ.filter fun v ↦ D T ωT v = 0).card =
    (Finset.univ.filter fun v ↦ D S ωS v = 0).card +
      (Finset.univ.filter fun v ↦ N v = 0).card
  have card {I : Type u} [Fintype I] (p : I → Prop) [DecidablePred p] :
      (Finset.univ.filter p).card = ∑ v : I, if p v then (1 : ℕ) else 0 := by
    simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) p Finset.univ).symm
  calc
    _ = ∑ v : T, if D T ωT v = 0 then (1 : ℕ) else 0 := card _
    _ = (∑ v : S, if D S ωS v = 0 then (1 : ℕ) else 0) +
        ∑ v : {v : T // v.val ∉ S}, if N v = 0 then (1 : ℕ) else 0 := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun v : T ↦ v.val ∈ S)]
      congr 1
      · symm
        apply Fintype.sum_equiv (equivOldPlaces F hST)
        intro v
        change (if D S ωS v = 0 then 1 else 0) =
          (if D T ωT ⟨v.val, hST v.property⟩ = 0 then (1 : ℕ) else 0)
        simp only [D, hPhase v]
      · apply Finset.sum_congr rfl
        intro v _
        simp only [D, N, ite_eq_left (hNew v.val v.property)]
    _ = _ := congrArg₂ (· + ·) (card (fun v : S ↦ D S ωS v = 0)).symm
      (card (fun v : {v : T // v.val ∉ S} ↦ N v = 0)).symm

include hPhase hNew in
private theorem sLocalProductZetaContinued_pad_mul
    (a : {w : InfinitePlace F // w.IsReal} → ℂ × ℕ)
    (j : {w : InfinitePlace F // w.IsComplex} → ℂ × ℤ)
    (f : E F S) (z : ℂ)
    (hz : sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT) z ≠ 0) :
    sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT) z *
      sLocalProductZetaContinued F T (fun v ↦ μ v.val) ωT a j (sLocalBruhatTransition F hST f) z =
      sLocalMellinPaddingHaarMass F μ S T *
        sLocalProductZetaContinued F S (fun v ↦ μ v.val) ωS a j f z := by
  let χ := sLocalFiniteZetaPhases F S ωS
  let ψ := sLocalFiniteZetaPhases F T ωT
  let D := sLocalMellinPaddingDenominator F S ψ z
  let C := sLocalMellinPaddingHaarMass F μ S T
  let ZS := sLocalProductZetaContinued F S (fun v ↦ μ v.val) ωS a j
  let ZT := sLocalProductZetaContinued F T (fun v ↦ μ v.val) ωT a j
  change D * ZT (sLocalBruhatTransition F hST f) z = C * ZS f z
  have hf : f ∈ Submodule.span ℂ {g : E F S |
      ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (p : X F S), sLocalBruhatPure F S φ p = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, p, rfl⟩ := hf
    rw [sLocalBruhatTransition_pure]
    simp only [ZT, ZS, sLocalProductZetaContinued, sLocalFiniteZetaSchwartzTest,
      sLocalBruhatContractFinite_pure, map_smul, smul_eq_mul]
    have hfin : D * sLocalFiniteZetaContinued F T (fun v ↦ μ v.val) ψ z
          (sLocalFiniteExtend F S T p) =
        C * sLocalFiniteZetaContinued F S (fun v ↦ μ v.val) χ z p :=
      sLocalFiniteZetaContinued_pad_mul F hST μ χ ψ hPhase hNew p z hz
    rw [← mul_assoc]
    exact (congrArg (fun w : ℂ ↦ w * archimedeanNumberFieldZeta F
      complexTamagawaAngularMeasure a j z φ) hfin).trans (mul_assoc _ _ _)
  | zero =>
    simp [ZT, ZS, sLocalProductZetaContinued]
  | add f g _ _ hf hg =>
    simp only [map_add, ZT, ZS, sLocalProductZetaContinued] at hf hg ⊢
    rw [mul_add, hf, hg, ← mul_add]
  | smul c f _ hf =>
    simp only [map_smul, ZT, ZS, sLocalProductZetaContinued, smul_eq_mul] at hf ⊢
    rw [mul_left_comm D, hf, mul_left_comm c]

private abbrev ZS (f : E F S) :=
  sLocalProductZetaContinued F S (fun v ↦ μ v.val) ωS (sLocalRealArchParameters F S ωS)
    (sLocalComplexArchParameters F S ωS) f

private abbrev ZT (f : E F T) :=
  sLocalProductZetaContinued F T (fun v ↦ μ v.val) ωT (sLocalRealArchParameters F T ωT)
    (sLocalComplexArchParameters F T ωT) f

include hPhase hNew in
/-- Finite-stage padding changes the S-local Mellin germ by exactly the
new finite Euler factors and their Haar normalization. -/
theorem sLocalProductZetaContinued_pad_germ
    (ha : sLocalRealArchParameters F S ωS = sLocalRealArchParameters F T ωT)
    (hj : sLocalComplexArchParameters F S ωS = sLocalComplexArchParameters F T ωT)
    (f : E F S) (c : ℂ) :
    (fun z ↦ sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT) z *
      ZT F μ ωT (sLocalBruhatTransition F hST f) z) =ᶠ[𝓝[≠] c]
        fun z ↦ sLocalMellinPaddingHaarMass F μ S T * ZS F μ ωS f z := by
  filter_upwards [sLocalMellinPaddingDenominator_eventually_ne_zero F (S := S)
    (sLocalFiniteZetaPhases F T ωT) c] with z hz
  have h := sLocalProductZetaContinued_pad_mul F hST μ ωS ωT hPhase hNew
    (sLocalRealArchParameters F S ωS) (sLocalComplexArchParameters F S ωS) f z hz
  change _ * sLocalProductZetaContinued F T (fun v ↦ μ v.val) ωT
    (sLocalRealArchParameters F T ωT) (sLocalComplexArchParameters F T ωT) _ z = _
  rw [← ha, ← hj]
  exact h

include hPhase hNew in
/-- The same padding identity when the archimedean parameters are compared
through the original archimedean integrals on the positive half-plane. -/
theorem sLocalProductZetaContinued_pad_germ_of_archIntegral
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (hArch : ∀ φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ), ∀ z : ℂ, 0 < z.re →
      sLocalArchZetaIntegral F T (archimedeanMultiplicativeHaar F) ωT φ z =
        sLocalArchZetaIntegral F S (archimedeanMultiplicativeHaar F) ωS φ z)
    (f : E F S) (c : ℂ) :
    (fun z ↦ sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT) z *
      ZT F μ ωT (sLocalBruhatTransition F hST f) z) =ᶠ[𝓝[≠] c]
        fun z ↦ sLocalMellinPaddingHaarMass F μ S T * ZS F μ ωS f z := by
  let D := sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT)
  let C := sLocalMellinPaddingHaarMass F μ S T
  let g := sLocalBruhatTransition F hST f
  let A (z : ℂ) := D z * ZT F μ ωT g z
  let B (z : ℂ) := C * ZS F μ ωS f z
  have hA : Meromorphic A := fun z ↦
    (Finset.analyticAt_fun_prod _ (fun (v : {v : T // v.val ∉ S}) _ ↦
      finiteZetaDenominator_analytic F v.val.val (sLocalFiniteZetaPhases F T ωT v.val) z)).meromorphicAt.mul
      (sLocalProductZetaContinued_meromorphic F T (fun v ↦ μ v.val) ωT _ _ g z)
  have hB : Meromorphic B := fun z ↦ (MeromorphicAt.const C z).mul
    (sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) ωS _ _ f z)
  have hEq (z : ℂ) (hz : 0 < z.re) : A z = B z := by
    have hn : D z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦
      finiteZetaDenominator_ne_zero_of_pos F v.val.val (sLocalFiniteZetaPhases F T ωT v.val) z hz
    have he := sLocalProductZetaContinued_pad_mul F hST μ ωS ωT hPhase hNew
      (sLocalRealArchParameters F S ωS) (sLocalComplexArchParameters F S ωS) f z hn
    have hE : ZT F μ ωT g z = sLocalProductZetaContinued F T (fun v ↦ μ v.val) ωT
        (sLocalRealArchParameters F S ωS) (sLocalComplexArchParameters F S ωS) g z := by
      unfold ZT sLocalProductZetaContinued
      rw [archimedeanNumberFieldZeta_eq_sLocalArchZetaIntegral F T ωT _ hz,
        hArch _ z hz, ← archimedeanNumberFieldZeta_eq_sLocalArchZetaIntegral F S ωS _ hz]
    change D z * ZT F μ ωT g z = _
    rw [hE]
    exact he
  have hQ := planeMeromorphicFunctions_mk_eq_of_eqOn_right
    (⟨A, hA⟩ : meromorphicRepresentatives) ⟨B, hB⟩ (fun z hz ↦ hEq z hz)
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hQ
  change ∀ z : ℂ, (fun w ↦ A w - B w) =ᶠ[𝓝[≠] z] 0 at hQ
  filter_upwards [hQ c] with z hz
  exact sub_eq_zero.mp hz

end Joint

end

end Masullo
