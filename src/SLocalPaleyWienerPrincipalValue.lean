import SLocalPaleyWienerLevels
import SLocalPrincipalZeta

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev P := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F
variable (S : Finset (P F))

private theorem sLocalAdditiveModulus_mul_idele (u : (SAdeles F S)ˣ) (x : SAdeles F S) :
    sLocalAdditiveModulus F S (u.val * x) = sLocalIdeleNorm F S u * sLocalAdditiveModulus F S x := by
  rw [← sLocalAdditiveModulus_idele]
  change ((∏ v : InfinitePlace F, ‖u.val.1 v * x.1 v‖ ^ v.mult) *
    ∏ v : S, ‖u.val.2 v * x.2 v‖) = _
  simp only [norm_mul, mul_pow, Finset.prod_mul_distrib, sLocalAdditiveModulus]
  ring

private theorem sLocalExpSection_negative_arch (q : ℝ) (hq : 1 ≤ q) (v : InfinitePlace F) :
    q⁻¹ ≤ ‖(sLocalExpSection F S (Multiplicative.ofAdd (-Real.log q))).val.1 v‖ ^ v.mult := by
  have hpos : 0 < q := zero_lt_one.trans_le hq
  have he : Real.exp (-Real.log q) = q⁻¹ := by rw [Real.exp_neg, Real.exp_log hpos]
  rw [sLocalExpSection_arch_norm, ← Real.exp_nat_mul, ← he]
  apply Real.exp_le_exp.mpr
  have hdeg : 0 < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hv : v.mult ≤ Module.finrank ℚ F := by
    rw [← InfinitePlace.sum_mult_eq]
    exact Finset.single_le_sum (fun w _ ↦ Nat.zero_le w.mult) (Finset.mem_univ v)
  have hm : (v.mult : ℝ) / Module.finrank ℚ F ≤ 1 :=
    (div_le_one hdeg).mpr (by exact_mod_cast hv)
  calc
    -Real.log q ≤ (v.mult : ℝ) / Module.finrank ℚ F * -Real.log q :=
      le_mul_of_le_one_left (neg_nonpos.mpr (Real.log_nonneg hq)) hm
    _ = _ := by ring

private theorem sLocalPaleyWienerBox_negativeRay {q X : ℝ} (hq : 1 ≤ q) (hX : 0 ≤ X)
    (f : E F S) (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X)) :
    sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd (-Real.log q))) f ∈
      sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S (q * X)) := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd (-Real.log q))
  apply sLocalPaleyWienerTests_leftTranslate F S u _ _ _ f hf
  intro x hx
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · have h := hx.1 v
    change ‖u.val.1 v * x.1 v‖ ^ v.mult ≤ X at h
    rw [norm_mul, mul_pow] at h
    have h' := (mul_le_mul_of_nonneg_right (sLocalExpSection_negative_arch F S q hq v)
      (pow_nonneg (norm_nonneg _) _)).trans h
    exact (inv_mul_le_iff₀ (zero_lt_one.trans_le hq)).mp h'
  · have h := hx.2 v
    change ‖u.val.2 v * x.2 v‖ ≤ X at h
    rw [sLocalExpSection_finite, one_mul] at h
    exact h.trans (le_mul_of_one_le_left hX hq)

private theorem sLocalPaleyWienerRegion_negativeRay {q Y : ℝ} (hq : 1 ≤ q)
    (f : E F S) (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S Y)) :
    sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd (-Real.log q))) f ∈
      sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S (q * Y)) := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd (-Real.log q))
  apply sLocalPaleyWienerTests_leftTranslate F S u _ _ _ f hf
  intro x hx
  change sLocalAdditiveModulus F S (u.val * x) ≤ Y at hx
  rw [sLocalAdditiveModulus_mul_idele, sLocalIdeleNorm_expSection, Real.exp_neg,
    Real.exp_log (zero_lt_one.trans_le hq)] at hx
  exact (inv_mul_le_iff₀ (zero_lt_one.trans_le hq)).mp hx

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable {T : Finset (P F)} (ν : Measure (SLocalThetaNormOne F T)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (SLocalThetaNormOne F T))

local notation "Moment" => sLocalPaleyWienerMomentKernel F T
local notation "Trans" => sLocalHomogeneousThetaTranslate F T ν ω

/-- A class of modulus 1/q moves the absolute level at X into the
absolute level at qX, including the common moment constraint. -/
theorem sLocalAbsolutePaleyWienerThetaLevel_translate_contraction
    (hST : S ⊆ T) {q X : ℝ} (hq : 1 ≤ q) (hX : 0 ≤ X)
    (c : SIdeleQuotient F T) (hc : sLocalClassModulus F T c = q⁻¹) :
    MapsTo (Trans c)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) Moment)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S (q * X)) Moment) := by
  apply sLocalPaleyWienerThetaLevel_translate F T ν ω hST _ _ _ (Or.inr rfl) c
  intro f hf
  apply sLocalPaleyWiener_homogeneousTranslate F S ν ω hST _ _ c _ f hf
  intro t ht
  rw [hc, Real.log_inv] at ht
  subst t
  exact sLocalPaleyWienerStageTests_leftTranslate F S hST _ _
    (sLocalPaleyWienerBox_negativeRay F S hq hX)

/-- For product levels the same norm change gives the bound qY. -/
theorem sLocalInvariantPaleyWienerThetaLevel_translate_contraction
    (hST : S ⊆ T) {q Y : ℝ} (hq : 1 ≤ q)
    (c : SIdeleQuotient F T) (hc : sLocalClassModulus F T c = q⁻¹) :
    MapsTo (Trans c)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerRegion F S Y) Moment)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerRegion F S (q * Y)) Moment) := by
  apply sLocalPaleyWienerThetaLevel_translate F T ν ω hST _ _ _ (Or.inr rfl) c
  intro f hf
  apply sLocalPaleyWiener_homogeneousTranslate F S ν ω hST _ _ c _ f hf
  intro t ht
  rw [hc, Real.log_inv] at ht
  subst t
  exact sLocalPaleyWienerStageTests_leftTranslate F S hST _ _
    (sLocalPaleyWienerRegion_negativeRay F S hq)


private abbrev M := sLocalHomogeneousThetaKernel F T ν ω
private abbrev Q := SLocalHomogeneousThetaQuotient F T ν ω

private def uniformizerClass (v : T) : SIdeleQuotient F T :=
  QuotientGroup.mk (sLocalFiniteZetaInsert F T v (chosenFiniteUniformizer F v.val))

private abbrev residueSize (v : T) : ℝ := v.val.asIdeal.absNorm

private theorem residueSize_ge_one (v : T) : 1 ≤ residueSize F v := by
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).le

private theorem uniformizerClass_modulus (v : T) :
    sLocalClassModulus F T (uniformizerClass F v) = (residueSize F v)⁻¹ := by
  unfold uniformizerClass
  rw [sLocalClassModulus_mk, sLocalFiniteZetaInsert_norm,
    norm_finiteUniformizer F v.val _ (chosenFiniteUniformizer_spec F v.val)]

/-- The homogeneous principal-value difference at an unramified place. -/
private def principalValueDifference (v : T) : Q F ν ω →L[ℂ] Q F ν ω :=
  ContinuousLinearMap.id ℂ _ - Trans (uniformizerClass F v)

local instance : MeasurableSpace (SAdeles F T)ˣ := borel _
local instance : BorelSpace (SAdeles F T)ˣ := ⟨rfl⟩

private theorem thetaZetaIntegral_translate (z : ℂ) (u : (SAdeles F T)ˣ) (f : E F T) :
    sLocalThetaZetaIntegral F T ν ω (sLocalBruhatLeftTranslate F T u f) z =
      sLocalZetaWeight F T ω z (QuotientGroup.mk u) * sLocalThetaZetaIntegral F T ν ω f z := by
  let a : SIdeleQuotient F T := QuotientGroup.mk u
  let μ := sLocalClassHaar F T ν
  letI : μ.IsHaarMeasure := sLocalClassHaar_isHaar F T ν
  let χ := sLocalZetaWeight F T ω z
  let G (q : SIdeleQuotient F T) := χ q * sLocalThetaOperator F T (sLocalBruhatLeftTranslate F T u f) q
  change (∫ q, G q ∂μ) = χ a * (∫ q, χ q * sLocalThetaOperator F T f q ∂μ)
  rw [← integral_const_mul, ← integral_mul_left_eq_self G a]
  refine integral_congr_ae (.of_forall fun q ↦ ?_)
  change χ (a * q) * sLocalThetaOperator F T (sLocalBruhatLeftTranslate F T u f) (a * q) =
    χ a * (χ q * sLocalThetaOperator F T f q)
  rw [sLocalThetaOperator_leftTranslate, show (QuotientGroup.mk u : SIdeleQuotient F T) = a from rfl,
    inv_mul_cancel_left]
  exact (congrArg (fun c : ℂ ↦ c * sLocalThetaOperator F T f q)
    (sLocalZetaWeight_mul F T ω z a q)).trans (mul_assoc _ _ _)

variable (μ : Measure (SAdeles F T)ˣ) [μ.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F T) μ Measure.count (sLocalClassHaar F T ν))

include hν in
private theorem principalValueDifference_mkQ (v : T)
    (hv : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F T ω v)) (f : E F T) :
    principalValueDifference F ν ω v ((M F ν ω).mkQ f) =
      (M F ν ω).mkQ (sLocalWeilPrincipalValue F T v f) := by
  let u := sLocalFiniteZetaInsert F T v (chosenFiniteUniformizer F v.val)
  let t := sLocalBruhatLeftTranslate F T u f
  change (M F ν ω).mkQ f - Trans (QuotientGroup.mk u) ((M F ν ω).mkQ f) = _
  rw [sLocalHomogeneousThetaTranslate_mkQ, ← map_sub]
  apply (Submodule.Quotient.eq _).mpr
  simp only [M, sLocalHomogeneousThetaKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y
  let z := (1 : ℂ) + (y : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  let L := sLocalThetaZetaCLM F T ν ω z hz
  change L (f - t - sLocalWeilPrincipalValue F T v f) = 0
  rw [map_sub, map_sub]
  change sLocalThetaZetaIntegral F T ν ω f z - sLocalThetaZetaIntegral F T ν ω t z -
    sLocalThetaZetaIntegral F T ν ω (sLocalWeilPrincipalValue F T v f) z = 0
  rw [sLocalThetaZeta_weilPrincipalValue F T μ ν hν ω z v f hz,
    sLocalPrincipalZetaFactor_of_unramified F T ω z v hv,
    thetaZetaIntegral_translate F ν ω z u f]
  change _ - _ - (1 - sLocalZetaWeight F T ω z (QuotientGroup.mk u)) * _ = 0
  ring


private theorem homogeneousTranslate_commute (c d : SIdeleQuotient F T) :
    Commute (Trans c) (Trans d) := by
  apply ContinuousLinearMap.ext
  intro x
  change Trans c (Trans d x) = Trans d (Trans c x)
  rw [← sLocalHomogeneousThetaTranslate_mul, ← sLocalHomogeneousThetaTranslate_mul]
  exact congrArg (fun a ↦ Trans a x) (mul_comm c d)

private theorem principalValueDifference_commute_translate (v : T) (c : SIdeleQuotient F T) :
    Commute (principalValueDifference F ν ω v) (Trans c) := by
  let d := uniformizerClass F v
  apply ContinuousLinearMap.ext
  intro x
  change Trans c x - Trans d (Trans c x) = Trans c (x - Trans d x)
  rw [map_sub]
  exact congrArg (Trans c x - ·)
    (DFunLike.congr_fun (homogeneousTranslate_commute F ν ω d c).eq x)

private theorem principalValueDifference_commute (v w : T) :
    Commute (principalValueDifference F ν ω v) (principalValueDifference F ν ω w) := by
  let A := principalValueDifference F ν ω v
  let d := uniformizerClass F w
  apply ContinuousLinearMap.ext
  intro x
  change A (x - Trans d x) = A x - Trans d (A x)
  rw [map_sub]
  exact congrArg (A x - ·)
    (DFunLike.congr_fun (principalValueDifference_commute_translate F ν ω v d).eq x)

/-- The finite product of homogeneous principal-value differences. At
unramified places this is the descent of the actual Weil operator. -/
def sLocalPaleyWienerPrincipalValues (R : Finset T) : Q F ν ω →L[ℂ] Q F ν ω :=
  R.noncommProd (principalValueDifference F ν ω)
    (fun v _ w _ _ ↦ principalValueDifference_commute F ν ω v w)

/-- Product of the residue cardinalities at the selected places. -/
def sLocalPaleyWienerPrincipalScale (R : Finset T) : ℝ :=
  ∏ v ∈ R, residueSize F v

theorem sLocalPaleyWienerPrincipalScale_ge_one (R : Finset T) :
    1 ≤ sLocalPaleyWienerPrincipalScale F R :=
  Finset.one_le_prod fun v _ ↦ residueSize_ge_one F v

private theorem principalValues_insert (v : T) (R : Finset T) (hv : v ∉ R) :
    sLocalPaleyWienerPrincipalValues F ν ω (insert v R) =
      principalValueDifference F ν ω v * sLocalPaleyWienerPrincipalValues F ν ω R :=
  Finset.noncommProd_insert_of_notMem R v (principalValueDifference F ν ω) _ hv

private theorem actualPrincipalValues_insert (v : T) (R : Finset T) (hv : v ∉ R) :
    sLocalWeilPrincipalValues F T (insert v R) =
      sLocalWeilPrincipalValue F T v * sLocalWeilPrincipalValues F T R :=
  Finset.noncommProd_insert_of_notMem R v (sLocalWeilPrincipalValue F T) _ hv

include hν in
theorem sLocalPaleyWienerPrincipalValues_mkQ (R : Finset T)
    (hR : ∀ v ∈ R, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F T ω v)) (f : E F T) :
    sLocalPaleyWienerPrincipalValues F ν ω R ((M F ν ω).mkQ f) =
      (M F ν ω).mkQ (sLocalWeilPrincipalValues F T R f) := by
  induction R using Finset.induction_on generalizing f with
  | empty => rfl
  | insert v R hv ih =>
    have hu := hR v (Finset.mem_insert_self _ _)
    have hR' (w : T) (hw : w ∈ R) := hR w (Finset.mem_insert_of_mem hw)
    rw [principalValues_insert F ν ω v R hv, actualPrincipalValues_insert F v R hv]
    change principalValueDifference F ν ω v
      (sLocalPaleyWienerPrincipalValues F ν ω R ((M F ν ω).mkQ f)) =
      (M F ν ω).mkQ (sLocalWeilPrincipalValue F T v (sLocalWeilPrincipalValues F T R f))
    rw [ih hR' f, principalValueDifference_mkQ F ν ω μ hν v hu]

theorem sLocalPaleyWienerPrincipalValues_commute_translate (R : Finset T) (c : SIdeleQuotient F T) :
    Commute (sLocalPaleyWienerPrincipalValues F ν ω R) (Trans c) := by
  apply Commute.symm
  exact Finset.noncommProd_commute R _ _ _ (fun v _ ↦
    (principalValueDifference_commute_translate F ν ω v c).symm)

private theorem principalValues_mapsTo_family
    (A : ℝ → Submodule ℂ (Q F ν ω)) (hA : Monotone A)
    (htranslate : ∀ (v : T) (r : ℝ), 0 ≤ r →
      MapsTo (Trans (uniformizerClass F v)) (A r) (A (residueSize F v * r)))
    (R : Finset T) (r : ℝ) (hr : 0 ≤ r) :
    MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R) (A r)
      (A (sLocalPaleyWienerPrincipalScale F R * r)) := by
  induction R using Finset.induction_on with
  | empty =>
    intro x hx
    simp only [sLocalPaleyWienerPrincipalScale, Finset.prod_empty, one_mul]
    exact hx
  | insert v R hv ih =>
    have he : sLocalPaleyWienerPrincipalScale F (insert v R) =
        residueSize F v * sLocalPaleyWienerPrincipalScale F R :=
      Finset.prod_insert hv
    rw [principalValues_insert F ν ω v R hv, he, mul_assoc]
    intro x hx
    let y := sLocalPaleyWienerPrincipalValues F ν ω R x
    let b := sLocalPaleyWienerPrincipalScale F R * r
    have hb : 0 ≤ b :=
      mul_nonneg (Finset.prod_nonneg (fun w _ ↦ zero_le_one.trans (residueSize_ge_one F w))) hr
    have hy : y ∈ A b := ih hx
    have hby : b ≤ residueSize F v * b := le_mul_of_one_le_left hb (residueSize_ge_one F v)
    change y - Trans (uniformizerClass F v) y ∈ A (residueSize F v * b)
    exact (A _).sub_mem (hA hby hy) (htranslate v b hb hy)

theorem sLocalAbsolutePaleyWienerThetaLevel_principalValues
    (hST : S ⊆ T) (R : Finset T) {X : ℝ} (hX : 0 ≤ X) :
    MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) Moment)
      (sLocalPaleyWienerThetaLevel F T ν ω hST
        (sLocalPaleyWienerBox F S (sLocalPaleyWienerPrincipalScale F R * X)) Moment) :=
  principalValues_mapsTo_family F ν ω _ (fun _ _ h ↦
    sLocalPaleyWienerThetaLevel_mono F T ν ω hST Moment (sLocalPaleyWienerBox_mono F S h))
    (fun v _ hr ↦ sLocalAbsolutePaleyWienerThetaLevel_translate_contraction
      F S ν ω hST (residueSize_ge_one F v) hr _ (uniformizerClass_modulus F v)) R X hX

theorem sLocalInvariantPaleyWienerThetaLevel_principalValues
    (hST : S ⊆ T) (R : Finset T) {Y : ℝ} (hY : 0 ≤ Y) :
    MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerRegion F S Y) Moment)
      (sLocalPaleyWienerThetaLevel F T ν ω hST
        (sLocalPaleyWienerRegion F S (sLocalPaleyWienerPrincipalScale F R * Y)) Moment) :=
  principalValues_mapsTo_family F ν ω _ (fun _ _ h ↦
    sLocalPaleyWienerThetaLevel_mono F T ν ω hST Moment (sLocalPaleyWienerRegion_mono F S h))
    (fun v _ _ ↦ sLocalInvariantPaleyWienerThetaLevel_translate_contraction
      F S ν ω hST (residueSize_ge_one F v) _ (uniformizerClass_modulus F v)) R Y hY

/-- A numerator of radius X receives the principal-value range from
the level of radius X divided by the product of residue sizes. -/
theorem sLocalAbsolutePaleyWienerThetaLevel_principalValues_target
    (hST : S ⊆ T) (R : Finset T) {X : ℝ} (hX : 0 ≤ X) :
    MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R)
      (sLocalPaleyWienerThetaLevel F T ν ω hST
        (sLocalPaleyWienerBox F S (X / sLocalPaleyWienerPrincipalScale F R)) Moment)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) Moment) := by
  let q := sLocalPaleyWienerPrincipalScale F R
  have hq : 0 < q := zero_lt_one.trans_le (sLocalPaleyWienerPrincipalScale_ge_one F R)
  have he : q * (X / q) = X := by rw [mul_comm, div_mul_cancel₀ _ hq.ne']
  have h := sLocalAbsolutePaleyWienerThetaLevel_principalValues F S ν ω hST R
    (div_nonneg hX hq.le)
  change MapsTo _ _ (sLocalPaleyWienerThetaLevel F T ν ω hST
    (sLocalPaleyWienerBox F S (q * (X/q))) Moment : Set (Q F ν ω)) at h
  rwa [he] at h

theorem sLocalInvariantPaleyWienerThetaLevel_principalValues_target
    (hST : S ⊆ T) (R : Finset T) {Y : ℝ} (hY : 0 ≤ Y) :
    MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R)
      (sLocalPaleyWienerThetaLevel F T ν ω hST
        (sLocalPaleyWienerRegion F S (Y / sLocalPaleyWienerPrincipalScale F R)) Moment)
      (sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerRegion F S Y) Moment) := by
  let q := sLocalPaleyWienerPrincipalScale F R
  have hq : 0 < q := zero_lt_one.trans_le (sLocalPaleyWienerPrincipalScale_ge_one F R)
  have he : q * (Y / q) = Y := by rw [mul_comm, div_mul_cancel₀ _ hq.ne']
  have h := sLocalInvariantPaleyWienerThetaLevel_principalValues F S ν ω hST R
    (div_nonneg hY hq.le)
  change MapsTo _ _ (sLocalPaleyWienerThetaLevel F T ν ω hST
    (sLocalPaleyWienerRegion F S (q * (Y/q))) Moment : Set (Q F ν ω)) at h
  rwa [he] at h


/-- The ambient homogeneous space of tests with both moments zero. -/
def sLocalPaleyWienerMomentImage : Submodule ℂ (Q F ν ω) :=
  (Moment).map (M F ν ω).mkQ

theorem isClosed_sLocalPaleyWienerMomentImage :
    IsClosed (sLocalPaleyWienerMomentImage F ν ω : Set (Q F ν ω)) := by
  let P : E F T →L[ℂ] ℂ × ℂ :=
    (GlobalBruhat.polarEvaluation F).comp (E F T).subtypeL
  let D := Moment
  have hD : D = P.toLinearMap.ker := rfl
  letI : FiniteDimensional ℂ (↥(E F T) ⧸ D) := by
    rw [hD]
    exact FiniteDimensional.of_injective P.toLinearMap.quotKerEquivRange.toLinearMap
      P.toLinearMap.quotKerEquivRange.injective
  have hC : IsClosed (D : Set (E F T)) := by
    rw [hD]
    exact P.isClosed_ker
  let H := sLocalPaleyWienerMomentImage F ν ω
  rw [← (M F ν ω).isOpenQuotientMap_mkQL.isQuotientMap.isClosed_preimage]
  change IsClosed (H.comap (M F ν ω).mkQ : Set (E F T))
  apply Submodule.isClosed_mono_of_finiteDimensional_quotient hC
  intro f hf
  change (M F ν ω).mkQ f ∈ (Moment).map (M F ν ω).mkQ
  exact Submodule.mem_map.mpr ⟨f,hf,rfl⟩

theorem sLocalPaleyWienerThetaLevel_le_momentImage (hST : S ⊆ T) (K : Set (SAdeles F S)) :
    sLocalPaleyWienerThetaLevel F T ν ω hST K Moment ≤ sLocalPaleyWienerMomentImage F ν ω := by
  change closure (↑(((sLocalPaleyWienerStageTests F S hST K) ⊓ Moment).map
    (M F ν ω).mkQ) : Set (Q F ν ω)) ⊆ _
  apply closure_minimal _ (isClosed_sLocalPaleyWienerMomentImage F ν ω)
  exact Submodule.map_mono (f := (M F ν ω).mkQ) inf_le_right

theorem sLocalPaleyWienerPrincipalValues_mapsTo_momentImage (R : Finset T) :
    MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R)
      (sLocalPaleyWienerMomentImage F ν ω) (sLocalPaleyWienerMomentImage F ν ω) := by
  induction R using Finset.induction_on with
  | empty => exact fun _ h ↦ h
  | insert v R hv ih =>
    rw [principalValues_insert F ν ω v R hv]
    intro x hx
    obtain ⟨f,hf,he⟩ := Submodule.mem_map.mp (ih hx)
    let u := sLocalFiniteZetaInsert F T v (chosenFiniteUniformizer F v.val)
    change principalValueDifference F ν ω v (sLocalPaleyWienerPrincipalValues F ν ω R x) ∈ _
    rw [← he]
    change (M F ν ω).mkQ f - Trans (QuotientGroup.mk u) ((M F ν ω).mkQ f) ∈ _
    rw [sLocalHomogeneousThetaTranslate_mkQ, ← map_sub]
    exact Submodule.mem_map.mpr ⟨_, (Moment).sub_mem hf
      (sLocalPaleyWiener_leftTranslate_preserves_moments F u f hf),rfl⟩


def sLocalPrincipalValueLevelRestriction {A B : Submodule ℂ (Q F ν ω)}
    (L : Q F ν ω →L[ℂ] Q F ν ω)
    (h : MapsTo L A B) : A →L[ℂ] B :=
  (L.comp A.subtypeL).codRestrict B (fun x ↦ h x.property)

private theorem restriction_square {A B C D : Submodule ℂ (Q F ν ω)}
    (hAB : A ≤ B) (hCD : C ≤ D) (L : Q F ν ω →L[ℂ] Q F ν ω)
    (hAC : MapsTo L A C) (hBD : MapsTo L B D) :
    (sLocalPrincipalValueLevelRestriction F ν ω L hBD).comp
        (sLocalPrincipalValueLevelRestriction F ν ω (ContinuousLinearMap.id ℂ _) hAB) =
      (sLocalPrincipalValueLevelRestriction F ν ω (ContinuousLinearMap.id ℂ _) hCD).comp
        (sLocalPrincipalValueLevelRestriction F ν ω L hAC) :=
  ContinuousLinearMap.ext fun _ ↦ Subtype.ext rfl

include hν in
/-- Corrected Proposition 7.3.3.2. The invariant vertical bound is qY.
The bottom horizontal inclusion uses an invariant level also large enough
to contain the whole absolute output level. -/
theorem sLocalPaleyWienerPrincipalValues_diagram
    (hST : S ⊆ T) (R : Finset T)
    (hR : ∀ v ∈ R, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F T ω v))
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hXY : X ^ (Fintype.card (InfinitePlace F) + S.card) ≤ Y) :
    let q := sLocalPaleyWienerPrincipalScale F R
    let d := Fintype.card (InfinitePlace F) + S.card
    let A := sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) Moment
    let A' := sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S (q*X)) Moment
    let B := sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerRegion F S Y) Moment
    let B' := sLocalPaleyWienerThetaLevel F T ν ω hST
      (sLocalPaleyWienerRegion F S (max (q*Y) ((q*X)^d))) Moment
    let H := sLocalPaleyWienerMomentImage F ν ω
    let P := sLocalPaleyWienerPrincipalValues F ν ω R
    (∀ f : E F T, P ((M F ν ω).mkQ f) =
      (M F ν ω).mkQ (sLocalWeilPrincipalValues F T R f)) ∧
    (∀ c : SIdeleQuotient F T, Commute P (Trans c)) ∧
    ∃ (hAB : A ≤ B) (hBH : B ≤ H) (hAB' : A' ≤ B') (hBH' : B' ≤ H)
      (hA : MapsTo P A A') (hB : MapsTo P B B') (hH : MapsTo P H H),
      let idQ := ContinuousLinearMap.id ℂ (Q F ν ω)
      (sLocalPrincipalValueLevelRestriction F ν ω P hB).comp
          (sLocalPrincipalValueLevelRestriction F ν ω idQ hAB) =
        (sLocalPrincipalValueLevelRestriction F ν ω idQ hAB').comp
          (sLocalPrincipalValueLevelRestriction F ν ω P hA) ∧
      (sLocalPrincipalValueLevelRestriction F ν ω P hH).comp
          (sLocalPrincipalValueLevelRestriction F ν ω idQ hBH) =
        (sLocalPrincipalValueLevelRestriction F ν ω idQ hBH').comp
          (sLocalPrincipalValueLevelRestriction F ν ω P hB) := by
  dsimp only
  let q := sLocalPaleyWienerPrincipalScale F R
  let d := Fintype.card (InfinitePlace F) + S.card
  have hq : 0 ≤ q :=
    Finset.prod_nonneg fun v _ ↦ zero_le_one.trans (residueSize_ge_one F v)
  have hmono := sLocalPaleyWienerThetaLevel_mono F T ν ω hST Moment
  have hAB := (sLocalAbsolutePaleyWienerThetaLevel_le_invariant F T ν ω hST hX.le Moment).trans
    (hmono (sLocalPaleyWienerRegion_mono F S hXY))
  have hAB' := (sLocalAbsolutePaleyWienerThetaLevel_le_invariant F T ν ω hST
    (mul_nonneg hq hX.le) Moment).trans
      (hmono (sLocalPaleyWienerRegion_mono F S (le_max_right (q*Y) ((q*X)^d))))
  have hB := (sLocalInvariantPaleyWienerThetaLevel_principalValues F S ν ω hST R hY.le).mono_right
    (hmono (sLocalPaleyWienerRegion_mono F S (le_max_left (q*Y) ((q*X)^d))))
  refine ⟨sLocalPaleyWienerPrincipalValues_mkQ F ν ω μ hν R hR,
    sLocalPaleyWienerPrincipalValues_commute_translate F ν ω R, hAB,
    sLocalPaleyWienerThetaLevel_le_momentImage F S ν ω hST _, hAB',
    sLocalPaleyWienerThetaLevel_le_momentImage F S ν ω hST _,
    sLocalAbsolutePaleyWienerThetaLevel_principalValues F S ν ω hST R hX.le,
    hB, sLocalPaleyWienerPrincipalValues_mapsTo_momentImage F ν ω R, ?_, ?_⟩
  · exact restriction_square F ν ω _ _ _ _ _
  · exact restriction_square F ν ω _ _ _ _ _

/-- The source's upper-row numerical comparison does not imply the same
comparison after multiplying both radii by a common factor. -/
theorem paleyWiener_scale_comparison_at_one {q : ℝ} {d : ℕ} (hq : 1 < q) (hd : 1 < d) :
    (1 : ℝ)^d ≤ 1 ∧ q*1 < (q*1)^d := by
  exact ⟨by simp, by simpa using pow_lt_pow_right₀ hq hd⟩

end

end Masullo
