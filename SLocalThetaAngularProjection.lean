import SLocalThetaShellReduction
import LFOpenMapping
import StrictQuotientStages
import StrongDualNuclearPermanence
import QuotientDuals
import Mathlib.Algebra.Group.Pi.Units

open Bornology Function IsDedekindDomain MeasureTheory NumberField Set Topology UniformSpace
open scoped Classical ComplexOrder NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Theta (S : Finset (Place F)) := SLocalThetaQuotient F S

variable (S : Finset (Place F))
private abbrev C := (w : S) → w.val.adicCompletion F
private abbrev B := locallyConstantTests (C F S)

variable (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
private abbrev U := ∀ w : S, H w

local instance angularFiniteTopology : TopologicalSpace (B F S) := finestLocallyConvexTopology _
local instance angularTensorTopology : TopologicalSpace (Arch F ⊗[ℂ] B F S) :=
  inductiveTensorTopology _ _

local instance angularMulAction : MulAction (U F S H) (C F S) where
  smul a x w := (a w).val.val * x w
  one_smul x := funext fun w ↦ one_mul (x w)
  mul_smul a b x := funext fun w ↦ mul_assoc (a w).val.val (b w).val.val (x w)

local instance angularContinuousSMul : ContinuousSMul (U F S H) (C F S) where
  continuous_smul := continuous_pi fun w ↦
    (Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply w).comp continuous_fst))).mul
      ((continuous_apply w).comp continuous_snd)

private def angularAction : U F S H →* (B F S →ₗ[ℂ] B F S) where
  toFun a := locallyConstantTestTranslate (C F S) a
  map_one' := by ext f x; simp [locallyConstantTestTranslate]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val ((a * b)⁻¹ • x) = f.val (b⁻¹ • a⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

private theorem angularAction_orbit (ψ : B F S) :
    IsLocallyConstant (fun a ↦ angularAction F S H a ψ) :=
  locallyConstantTestTranslate_orbit_locallyConstant _ ψ

/-- The S-idèle with trivial infinite coordinates and the given local units. -/
def angularLocalIdele (a : U F S H) : (SAdeles F S)ˣ :=
  MulEquiv.prodUnits.symm (1, MulEquiv.piUnits.symm (fun w ↦ (a w).val))

private theorem angularTranslate_eq (a : U F S H) (f : Test F S) :
    sLocalBruhatFiniteMap F S (angularAction F S H a) f =
      sLocalBruhatLeftTranslate F S (angularLocalIdele F S H a) f := by
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ ψ =>
    change sLocalBruhatFiniteMap F S (angularAction F S H a) (sLocalBruhatPure F S φ ψ) =
      sLocalBruhatLeftTranslate F S (angularLocalIdele F S H a) (sLocalBruhatPure F S φ ψ)
    rw [sLocalBruhatFiniteMap_pure]
    apply Subtype.ext
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    funext z
    change GlobalBruhat.evaluation F z (sLocalBruhatPure F S φ (angularAction F S H a ψ)).val =
      GlobalBruhat.evaluation F z (sLocalBruhatLeftTranslate F S (angularLocalIdele F S H a)
        (sLocalBruhatPure F S φ ψ)).val
    rw [sLocalBruhatRestriction_reconstruct F S, sLocalBruhatRestriction_reconstruct F S,
      sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
    let x := sAdelesProjection F S z
    have h₁ : ((angularLocalIdele F S H a).inv * x).1 = x.1 := by
      change (1 : InfiniteAdeleRing F) * x.1 = x.1
      exact one_mul _
    have h₂ : ((angularLocalIdele F S H a).inv * x).2 = a⁻¹ • x.2 := rfl
    rw [h₁, h₂]
    rfl

variable (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
variable (hn : ∀ (w : S) (a : H w), ‖a.val.val‖ = 1)

include hH hn in
private theorem compactAngularFactors (w : S) : CompactSpace (H w) := by
  letI := principalIntegralUnits_compactSpace F w.val
  have hK : IsCompact (principalIntegralUnits F w.val : Set (w.val.adicCompletion F)ˣ) :=
    isCompact_iff_compactSpace.mpr inferInstance
  exact isCompact_iff_compactSpace.mp
    (hK.of_isClosed_subset ((H w).isClosed_of_isOpen (hH w)) (fun a ha ↦ hn w ⟨a, ha⟩))

include hH hn in
private theorem angularCompact : CompactSpace (U F S H) := by
  letI (w : S) := compactAngularFactors F S H hH hn w
  infer_instance

local instance angularMeasurable : MeasurableSpace (U F S H) := borel _
local instance angularBorel : BorelSpace (U F S H) := ⟨rfl⟩

private def angularHaar (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hn : ∀ (w : S) (a : H w), ‖a.val.val‖ = 1) : Measure (U F S H) :=
  letI := angularCompact F S H hH hn
  Measure.haarMeasure ⊤

local instance angularHaar_isHaar : (angularHaar F S H hH hn).IsHaarMeasure := by
  letI := angularCompact F S H hH hn
  unfold angularHaar
  infer_instance

private theorem angularHaar_univ : angularHaar F S H hH hn univ = 1 := by
  letI := angularCompact F S H hH hn
  exact Measure.haarMeasure_self

include hH hn in
private def angularAverage : B F S →ₗ[ℂ] B F S :=
  letI := angularCompact F S H hH hn
  fixedOrbitAverage (angularAction F S H) (angularHaar F S H hH hn) (angularAction_orbit F S H)

private theorem coordinateInvariance_iff (ψ : B F S) :
    (∀ w, thetaFiniteInvariantAt F S w (H w) ψ) ↔
      (∀ a, angularAction F S H a ψ = ψ) := by
  constructor
  · intro hf a
    have hprod (t : Finset S) (x : C F S) :
        ψ.val (fun w ↦ if w ∈ t then (a w).val.inv * x w else x w) = ψ.val x := by
      induction t using Finset.induction_on with
      | empty => simp
      | insert i t hi ih =>
        let y : C F S := fun w ↦ if w ∈ t then (a w).val.inv * x w else x w
        have he : (fun w ↦ if w ∈ insert i t then (a w).val.inv * x w else x w) =
            Function.update y i ((a i).val.inv * x i) := by
          funext w
          by_cases h : w = i
          · subst w
            simp
          · simp [h, y]
        rw [he]
        have h := hf i ((a i)⁻¹) y (x i)
        have hy : y i = x i := by simp [y, hi]
        change ψ.val (Function.update y i ((a i).val.inv * x i)) =
          ψ.val (Function.update y i (x i)) at h
        rw [h, ← hy, Function.update_eq_self]
        exact ih
    apply Subtype.ext
    funext x
    change ψ.val (fun w ↦ (a w).val.inv * x w) = ψ.val x
    simpa only [Finset.mem_univ, ite_true] using hprod Finset.univ x
  · intro hf w a x y
    let g : U F S H := Function.update 1 w a⁻¹
    have he := congrArg (fun ψ : B F S ↦ ψ.val (Function.update x w y)) (hf g)
    change ψ.val (g⁻¹ • Function.update x w y) = _ at he
    have hx : g⁻¹ • Function.update x w y = Function.update x w (a.val.val * y) := by
      funext i
      by_cases hi : i = w
      · subst i
        change ((g w)⁻¹).val.val * Function.update x w y w = _
        simp [g, Function.update_self]
      · change ((g i)⁻¹).val.val * Function.update x w y i = _
        simp [g, Function.update_of_ne hi]
    rwa [hx] at he

private theorem angularAverage_invariant (ψ : B F S) :
    ∀ w, thetaFiniteInvariantAt F S w (H w) (angularAverage F S H hH hn ψ) := by
  letI := angularCompact F S H hH hn
  exact (coordinateInvariance_iff F S H _).mpr
    (fixedOrbitAverage_fixed _ _ _ _)

private theorem angularAverage_of_invariant (ψ : B F S)
    (hψ : ∀ w, thetaFiniteInvariantAt F S w (H w) ψ) :
    angularAverage F S H hH hn ψ = ψ := by
  letI := angularCompact F S H hH hn
  exact fixedOrbitAverage_of_fixed _ _ _ (angularHaar_univ F S H hH hn) ψ
    ((coordinateInvariance_iff F S H ψ).mp hψ)

private def angularTestAverage : Test F S →L[ℂ] Test F S :=
  sLocalBruhatFiniteMap F S (angularAverage F S H hH hn)

private theorem finiteMaps_orbit (f : Test F S) :
    IsLocallyConstant (fun a ↦ sLocalBruhatFiniteMap F S (angularAction F S H a) f) := by
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact IsLocallyConstant.const 0
  | add x y hx hy =>
    simp only [map_add]
    exact (hx.prodMk hy).comp (fun p ↦ p.1 + p.2)
  | tmul φ ψ =>
    change IsLocallyConstant (fun a ↦ sLocalBruhatFiniteMap F S (angularAction F S H a)
      (sLocalBruhatPure F S φ ψ))
    simp_rw [sLocalBruhatFiniteMap_pure]
    exact (angularAction_orbit F S H ψ).comp (sLocalBruhatPure F S φ)

private theorem angularTestAverage_apply (f : Test F S) (ℓ : Test F S →ₗ[ℂ] ℂ) :
    ℓ (angularTestAverage F S H hH hn f) =
      ∫ a, ℓ (sLocalBruhatFiniteMap F S (angularAction F S H a) f) ∂angularHaar F S H hH hn := by
  letI := angularCompact F S H hH hn
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    symm
    apply integral_add
    · exact ((finiteMaps_orbit F S H (e x)).comp ℓ).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact ((finiteMaps_orbit F S H (e y)).comp ℓ).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  | tmul φ ψ =>
    change ℓ (sLocalBruhatFiniteMap F S (angularAverage F S H hH hn) (sLocalBruhatPure F S φ ψ)) =
      ∫ a, ℓ (sLocalBruhatFiniteMap F S (angularAction F S H a)
        (sLocalBruhatPure F S φ ψ)) ∂angularHaar F S H hH hn
    simp_rw [sLocalBruhatFiniteMap_pure]
    exact fixedOrbitAverage_apply _ _ _ ψ (ℓ.comp (sLocalBruhatPure F S φ))

private theorem angularTestAverage_memKernel {f : Test F S}
    (hf : f ∈ (sLocalThetaOperator F S).ker) :
    angularTestAverage F S H hH hn f ∈ (sLocalThetaOperator F S).ker := by
  apply LinearMap.mem_ker.mpr
  funext g
  let ℓ := (LinearMap.proj g).comp (sLocalThetaOperator F S)
  change ℓ (angularTestAverage F S H hH hn f) = 0
  rw [angularTestAverage_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with a
  rw [angularTranslate_eq]
  have he : (Submodule.Quotient.mk
      (sLocalBruhatLeftTranslate F S (angularLocalIdele F S H a) f) : Theta F S) = 0 := by
    rw [← sLocalThetaTranslateIdeles_mk, (Submodule.Quotient.mk_eq_zero _).mpr hf, map_zero]
  exact congrFun (LinearMap.mem_ker.mp ((Submodule.Quotient.mk_eq_zero _).mp he)) g

/-- Average the S-local theta quotient over a product of open integral-unit
subgroups. The operator is continuous in the intrinsic quotient topology. -/
def sLocalThetaAngularAverage : Theta F S →L[ℂ] Theta F S := by
  let K := (sLocalThetaOperator F S).ker
  refine K.liftQL (K.mkQL.comp (angularTestAverage F S H hH hn)) ?_
  intro f hf
  exact LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero K).mpr
    (angularTestAverage_memKernel F S H hH hn hf))

/-- A quotient endomorphism that intertwines each integral-unit translation
also intertwines their angular projection. -/
theorem sLocalThetaAngularAverage_commutes (P : Theta F S →L[ℂ] Theta F S)
    (hP : ∀ (a : U F S H) (q : Theta F S),
      P (sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a) q) =
        sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a) (P q))
    (q : Theta F S) :
    sLocalThetaAngularAverage F S H hH hn (P q) =
      P (sLocalThetaAngularAverage F S H hH hn q) := by
  let A := sLocalThetaAngularAverage F S H hH hn
  have hp (x : Theta F S) (ℓ : Theta F S →ₗ[ℂ] ℂ) :
      ℓ (A x) = ∫ a, ℓ (sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a) x)
        ∂angularHaar F S H hH hn := by
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h := angularTestAverage_apply F S H hH hn f (ℓ.comp (sLocalThetaOperator F S).ker.mkQ)
    simp only [sLocalThetaTranslateIdeles_mk]
    change ℓ ((sLocalThetaOperator F S).ker.mkQ (angularTestAverage F S H hH hn f)) =
      ∫ a, ℓ ((sLocalThetaOperator F S).ker.mkQ
        (sLocalBruhatLeftTranslate F S (angularLocalIdele F S H a) f)) ∂angularHaar F S H hH hn
    simpa only [LinearMap.comp_apply,angularTranslate_eq] using h
  change A (P q) = P (A q)
  by_contra h
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr h)
  apply hℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he := hp q (ℓ.comp P.toLinearMap)
  rw [hp (P q) ℓ]
  simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hP] using he.symm

private theorem angularProjection_maps_into (q : Theta F S) :
    sLocalThetaAngularAverage F S H hH hn q ∈ sLocalThetaInvariantTestSpan F S H := by
  let e := sLocalBruhatTensorEquiv F S
  let K := (sLocalThetaOperator F S).ker
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective K q
  obtain ⟨t, rfl⟩ := e.surjective f
  let L := (K.mkQ.comp (angularTestAverage F S H hH hn).toLinearMap).comp e.toLinearEquiv.toLinearMap
  change L t ∈ sLocalThetaInvariantTestSpan F S H
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul φ ψ =>
    change K.mkQ (sLocalBruhatFiniteMap F S (angularAverage F S H hH hn)
      (sLocalBruhatPure F S φ ψ)) ∈ _
    rw [sLocalBruhatFiniteMap_pure]
    exact Submodule.subset_span ⟨φ, _, angularAverage_invariant F S H hH hn ψ, rfl⟩

private theorem angularProjection_fixes (q : Theta F S)
    (hq : q ∈ sLocalThetaInvariantTestSpan F S H) :
    sLocalThetaAngularAverage F S H hH hn q = q := by
  let W := (sLocalThetaAngularAverage F S H hH hn -
    ContinuousLinearMap.id ℂ (Theta F S)).toLinearMap.ker
  have he : sLocalThetaInvariantTestSpan F S H ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, ψ, hψ, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (sLocalThetaOperator F S).ker.mkQ (sLocalBruhatFiniteMap F S
      (angularAverage F S H hH hn) (sLocalBruhatPure F S φ ψ)) -
      (sLocalThetaOperator F S).ker.mkQ (sLocalBruhatPure F S φ ψ) = 0
    rw [sLocalBruhatFiniteMap_pure, angularAverage_of_invariant F S H hH hn ψ hψ, sub_self]
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (he hq))

include hH hn in
/-- A quotient class fixed by the integral-unit translations lies in the
span of classes of invariant tests. -/
theorem mem_sLocalThetaInvariantTestSpan_of_fixed (q : Theta F S)
    (hq : ∀ a : U F S H, sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a) q = q) :
    q ∈ sLocalThetaInvariantTestSpan F S H := by
  have hfix : sLocalThetaAngularAverage F S H hH hn q = q := by
    let K := (sLocalThetaOperator F S).ker
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective K q
    change K.mkQ f = q at hf
    rw [← hf]
    change K.mkQ (angularTestAverage F S H hH hn f) = K.mkQ f
    apply (Submodule.Quotient.eq K).mpr
    apply LinearMap.mem_ker.mpr
    funext g
    let ℓ := (LinearMap.proj g).comp (sLocalThetaOperator F S)
    change ℓ (angularTestAverage F S H hH hn f - f) = 0
    rw [map_sub, angularTestAverage_apply]
    have hval (a : U F S H) :
        ℓ (sLocalBruhatFiniteMap F S (angularAction F S H a) f) = ℓ f := by
      rw [angularTranslate_eq]
      have he := hq a
      rw [← hf] at he
      change sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a)
        (Submodule.Quotient.mk f) = Submodule.Quotient.mk f at he
      rw [sLocalThetaTranslateIdeles_mk] at he
      have hz := LinearMap.mem_ker.mp ((Submodule.Quotient.eq K).mp he)
      exact sub_eq_zero.mp (by simpa only [map_sub, Pi.sub_apply, Pi.zero_apply, ℓ,
        LinearMap.comp_apply, LinearMap.proj_apply] using congrFun hz g)
    simp [hval, measureReal_def, angularHaar_univ]
  rw [← hfix]
  exact angularProjection_maps_into F S H hH hn q

/-- The angular test span consists of classes fixed by the corresponding
integral-unit translations. -/
theorem sLocalThetaInvariantTestSpan_fixed (q : Theta F S)
    (hq : q ∈ sLocalThetaInvariantTestSpan F S H) (a : U F S H) :
    sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a) q = q := by
  let T := sLocalThetaTranslateIdeles F S (angularLocalIdele F S H a)
  let K := (T - ContinuousLinearMap.id ℂ (Theta F S)).toLinearMap.ker
  have hle : sLocalThetaInvariantTestSpan F S H ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ,ψ,hψ,rfl⟩
    apply LinearMap.mem_ker.mpr
    change T (Submodule.Quotient.mk (sLocalBruhatPure F S φ ψ)) -
      Submodule.Quotient.mk (sLocalBruhatPure F S φ ψ) = 0
    dsimp only [T]
    rw [sLocalThetaTranslateIdeles_mk, ← angularTranslate_eq, sLocalBruhatFiniteMap_pure,
      (coordinateInvariance_iff F S H ψ).mp hψ a, sub_self]
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hle hq))

/-- The invariant span is complemented in the S-local quotient. -/
def sLocalThetaAngularRetraction : Theta F S →L[ℂ] sLocalThetaInvariantTestSpan F S H :=
  (sLocalThetaAngularAverage F S H hH hn).codRestrict _ (angularProjection_maps_into F S H hH hn)

theorem sLocalThetaAngularRetraction_leftInverse :
    LeftInverse (sLocalThetaAngularRetraction F S H hH hn)
      ((sLocalThetaInvariantTestSpan F S H).subtypeL) :=
  fun q ↦ Subtype.ext (angularProjection_fixes F S H hH hn q.val q.property)

private theorem archProduct_isFrechet (J : Type*) [Finite J] :
    IsFrechetTVS (J → Arch F) := by
  letI : CompleteSpace (Arch F) := completeSpace_schwartzMap
  letI : PolynormableSpace ℂ (Arch F) :=
    (schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).toPolynormableSpace
  letI : TopologicalSpace.MetrizableSpace (Arch F) := by
    have : (uniformity (Arch F)).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero (Arch F)]
      infer_instance
    exact UniformSpace.metrizableSpace
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- A complemented subspace of a countable Fréchet-final space inherits the
topology of any continuous surjective parametrization by a Fréchet space. -/
private theorem frechet_of_complemented_parametrization
    {E X : Type*} {A : ℕ → Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [PolynormableSpace ℂ E]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)] [∀ n, TopologicalSpace (A n)]
    (i : ∀ n, A n →L[ℂ] E) (hi : ∀ y : E, ∃ n, y ∈ range (i n))
    (hfinal : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (i n).toLinearMap)) → Continuous p)
    (hA : ∀ n, IsFrechetTVS (A n)) (hX : IsFrechetTVS X)
    (W : Submodule ℂ E) (r : E →L[ℂ] W) (hr : LeftInverse r W.subtypeL)
    (q : X →L[ℂ] W) (hq : Surjective q) :
    IsFrechetTVS W ∧ ∃ e : (X ⧸ q.ker) ≃L[ℂ] W,
      e.toContinuousLinearMap.comp q.ker.mkQL = q := by
  choose hadd hpoly hmetric hcomplete using hA
  letI : ∀ n, IsTopologicalAddGroup (A n) := hadd
  letI : ∀ n, UniformSpace (A n) := fun _ ↦ IsTopologicalAddGroup.rightUniformSpace _
  letI : ∀ n, IsUniformAddGroup (A n) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  letI : ∀ n, CompleteSpace (A n) := hcomplete
  letI : ∀ n, PolynormableSpace ℂ (A n) := hpoly
  letI : ∀ n, TopologicalSpace.MetrizableSpace (A n) := hmetric
  letI (n : ℕ) : FirstCountableTopology (A n) := inferInstance
  letI (n : ℕ) : T2Space (A n) := inferInstance
  letI (n : ℕ) : ContinuousSMul ℂ (A n) := (PolynormableSpace.withSeminorms ℂ (A n)).continuousSMul
  letI (n : ℕ) : LocallyConvexSpace ℂ (A n) := by
    letI : Module ℝ (A n) := Module.restrictScalars ℝ ℂ (A n)
    letI : IsScalarTower ℝ ℂ (A n) := IsScalarTower.restrictScalars ℝ ℂ (A n)
    letI : LocallyConvexSpace ℝ (A n) :=
      (PolynormableSpace.withSeminorms ℂ (A n)).toLocallyConvexSpace
    exact LocallyConvexSpace.ofBasisZero ℂ (A n) id
      (fun s : Set (A n) ↦ s ∈ nhds 0 ∧ Convex ℝ s)
      (LocallyConvexSpace.convex_basis_zero ℝ (A n))
      (fun s hs ↦ convex_of_nonneg_surjective_algebraMap ℂ
        (fun _ h ↦ RCLike.nonneg_iff_exists_ofReal.mp h) hs.2)
  obtain ⟨hxadd, hxpoly, hxmet, hxcomplete⟩ := hX
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := hxcomplete
  letI : TopologicalSpace.MetrizableSpace X := hxmet
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  let j (n : ℕ) := r.comp (i n)
  have hj (w : W) : ∃ n, w ∈ range (j n) := by
    obtain ⟨n, a, ha⟩ := hi w.val
    exact ⟨n, a, (congrArg r ha).trans (hr w)⟩
  have hW (p : Seminorm ℂ W) (hp : ∀ n, Continuous (p.comp (j n).toLinearMap)) :
      Continuous p := by
    have hc : Continuous (p.comp r.toLinearMap) := hfinal _ hp
    have he : (p.comp r.toLinearMap).comp W.subtype = p := by
      ext x
      exact congrArg p (hr x)
    rw [← he]
    exact hc.comp continuous_subtype_val
  obtain ⟨_, e, he⟩ := lf_open_mapping j (fun _ : ℕ ↦ ContinuousLinearMap.id ℂ X)
    hj (fun x ↦ ⟨0, x, rfl⟩) hW q hq
  let K := q.ker
  have hK : IsClosed (K : Set X) := q.isClosed_ker
  have hQ := isFrechetTVS_closedQuotient (show IsFrechetTVS X from
    ⟨hxadd, hxpoly, hxmet, hxcomplete⟩) K hK
  obtain ⟨hqadd, hqpoly, hqmet, hqcomplete⟩ := hQ
  letI : TopologicalSpace.MetrizableSpace (X ⧸ K) := hqmet
  letI : UniformSpace (X ⧸ K) := IsTopologicalAddGroup.rightUniformSpace _
  letI : UniformSpace W := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (X ⧸ K) := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup W := isUniformAddGroup_of_addCommGroup
  have hu : IsUniformInducing e.toLinearEquiv.toLinearMap.toAddMonoidHom :=
    AddMonoidHom.isUniformInducing_of_isInducing e.toHomeomorph.isInducing
  exact ⟨⟨inferInstance, inferInstance, e.symm.toHomeomorph.isEmbedding.metrizableSpace,
    (hu.completeSpace_congr e.surjective).mp hqcomplete⟩, e, he⟩

include hH hn in
private theorem invariantTestSpan_structure :
    IsFrechetTVS (sLocalThetaInvariantTestSpan F S H) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) →
        NuclearLocallyConvex.{u, u} (sLocalThetaInvariantTestSpan F S H)) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) →
        NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F)) →
        NuclearLocallyConvex.{u, u} (StrongDual ℂ (sLocalThetaInvariantTestSpan F S H))) := by
  letI : T2Space (Theta F S) := sLocalThetaQuotient_t2Space F S
  letI : PolynormableSpace ℂ (Theta F S) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  obtain ⟨J, L, hJ, hL⟩ := sLocalTheta_invariant_finiteTests_factor F S H hH hn
  let W := sLocalThetaInvariantTestSpan F S H
  let q : (J → Arch F) →L[ℂ] W := L.codRestrict W (fun x ↦ by
    change L x ∈ sLocalThetaInvariantTestSpan F S H
    rw [← hL]
    exact ⟨x, rfl⟩)
  have hq : Surjective q := by
    intro w
    obtain ⟨x, hx⟩ := show w.val ∈ L.toLinearMap.range from hL.symm ▸ w.property
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨A, _, _, _, D, hA, hfinal⟩ := sLocalThetaQuotient_exists_frechetStages F S
  letI : Finite J := hJ
  obtain ⟨hW, e, _⟩ := frechet_of_complemented_parametrization D.incl D.exhaust hfinal hA
    (archProduct_isFrechet F J) W (sLocalThetaAngularRetraction F S H hH hn)
    (sLocalThetaAngularRetraction_leftInverse F S H hH hn) q hq
  have hprod (hN : NuclearLocallyConvex.{u, u} (Arch F)) :
      NuclearLocallyConvex.{u, u} (J → Arch F) :=
    nuclearLocallyConvex_pi (fun _ ↦ hN)
  refine ⟨hW, ?_, ?_⟩
  · exact fun hN ↦ nuclearLocallyConvex_of_equiv e
      (nuclearLocallyConvex_quotient (hprod hN) q.ker q.isClosed_ker)
  · exact fun hN hD ↦ strongDual_nuclear_of_equiv e
      (strongDual_nuclear_of_closedQuotient q.ker q.isClosed_ker
        (archProduct_isFrechet F J) (hprod hN) (strongDual_nuclear_pi_finite (fun _ ↦ hD)))

include hH hn in
/-- Each invariant test span is Fréchet in the topology induced from the theta quotient. -/
theorem sLocalThetaInvariantTestSpan_isFrechet :
    IsFrechetTVS (sLocalThetaInvariantTestSpan F S H) :=
  (invariantTestSpan_structure F S H hH hn).1

include hH hn in
/-- Bounded families in a fixed angular stage lift to compact sets of S-local tests
whose image covers the original families. -/
theorem sLocalThetaInvariantTestSpan_bounded_lift
    (hN : NuclearLocallyConvex.{u, u} (Arch F))
    (B : Set (sLocalThetaInvariantTestSpan F S H)) (hB : IsVonNBounded ℂ B) :
    ∃ A : Set (sLocalBruhatImage F S), IsCompact A ∧
      (sLocalThetaInvariantTestSpan F S H).subtypeL '' B ⊆
        (sLocalThetaOperator F S).ker.mkQL '' A := by
  letI : T2Space (Theta F S) := sLocalThetaQuotient_t2Space F S
  letI : PolynormableSpace ℂ (Theta F S) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  obtain ⟨J, L, hJ, hL, U, hU⟩ := sLocalTheta_invariant_finiteTests_factor_with_lift F S H hH hn
  let W := sLocalThetaInvariantTestSpan F S H
  let q : (J → Arch F) →L[ℂ] W := L.codRestrict W (fun x ↦ by
    change L x ∈ sLocalThetaInvariantTestSpan F S H
    rw [← hL]
    exact ⟨x, rfl⟩)
  have hq : Surjective q := by
    intro w
    obtain ⟨x, hx⟩ := show w.val ∈ L.toLinearMap.range from hL.symm ▸ w.property
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨_, _, _, _, D, hA, hfinal⟩ := sLocalThetaQuotient_exists_frechetStages F S
  letI : Finite J := hJ
  have hf := archProduct_isFrechet F J
  obtain ⟨_, e, he⟩ := frechet_of_complemented_parametrization D.incl D.exhaust hfinal hA
    hf W (sLocalThetaAngularRetraction F S H hH hn)
    (sLocalThetaAngularRetraction_leftInverse F S H hH hn) q hq
  obtain ⟨C, hC, hcover⟩ := nuclearFrechet_quotient_compactLift q.ker q.isClosed_ker
    (nuclearLocallyConvex_pi (fun _ : J ↦ hN)) hf (hB.image e.symm.toContinuousLinearMap)
  refine ⟨U '' C, hC.image U.continuous, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hw' : e.symm w ∈ q.ker.mkQL '' C :=
    hcover.symm ▸ subset_closure ⟨w, hw, rfl⟩
  obtain ⟨x, hx, hqx⟩ := hw'
  refine ⟨U x, ⟨x, hx, rfl⟩, ?_⟩
  have hqx' : q x = w := (DFunLike.congr_fun he x).symm.trans
    ((congrArg e hqx).trans (e.apply_symm_apply w))
  exact (DFunLike.congr_fun hU x).trans (congrArg Subtype.val hqx')

include hH hn in
/-- Nuclearity of the archimedean Schwartz space passes to each invariant test span. -/
theorem sLocalThetaInvariantTestSpan_nuclear_of_arch
    (hN : NuclearLocallyConvex.{u, u} (Arch F)) :
    NuclearLocallyConvex.{u, u} (sLocalThetaInvariantTestSpan F S H) :=
  (invariantTestSpan_structure F S H hH hn).2.1 hN

include hH hn in
/-- The strong dual of an invariant test span is nuclear when the archimedean
Schwartz factor and its strong dual are nuclear. -/
theorem sLocalThetaInvariantTestSpan_strongDual_nuclear_of_arch
    (hN : NuclearLocallyConvex.{u, u} (Arch F))
    (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F))) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (sLocalThetaInvariantTestSpan F S H)) :=
  (invariantTestSpan_structure F S H hH hn).2.2 hN hD

end

end Masullo
