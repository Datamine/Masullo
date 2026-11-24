import GlobalPaleyWienerTrace
import HardySobolevJetProjections
import HeckeEulerProducts
import Mathlib.Data.Finset.Interval

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical CompactlySupported NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance globalSobolevPrincipalValuesIdeleClassMeasurableSpace : MeasurableSpace (Q F) := borel _
local instance globalSobolevPrincipalValuesIdeleClassBorelSpace : BorelSpace (Q F) := ⟨rfl⟩
local instance globalSobolevPrincipalValuesIdeleClassLocallyCompactSpace : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance globalSobolevPrincipalValuesIdeleClassT2Space : T2Space (Q F) := ideleClasses_hausdorff
local instance globalSobolevPrincipalValuesIdeleClassSecondCountableTopology : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev N := globalThetaSobolevCompletion F μ 0 0 0 s hs
private abbrev W (ω : PontryaginDual (K F)) :=
  globalAmbientSobolevIsotype F ω μ 0 0 s hs

/-- Translation in the zero-line Hilbert chart. -/
private abbrev translate (g : Q F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs g

/-- Class of the chosen uniformizer inserted at a single finite place. -/
def globalUniformizerClass (v : Place F) : Q F :=
  ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v))

/-- The printed finite-place principal-value difference on the ambient
zero-line Sobolev space. -/
def globalSobolevPrincipalValue (v : Place F) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  1 - translate F μ s hs (globalUniformizerClass F v)

private theorem translate_commute (g h : Q F) :
    Commute (translate F μ s hs g) (translate F μ s hs h) := by
  ext x : 1
  change translate F μ s hs g (translate F μ s hs h x) =
    translate F μ s hs h (translate F μ s hs g x)
  rw [← hardySobolevMulTranslation_mul, ← hardySobolevMulTranslation_mul, mul_comm g h]

private theorem globalSobolevPrincipalValue_commute (v w : Place F) :
    Commute (globalSobolevPrincipalValue F μ s hs v)
      (globalSobolevPrincipalValue F μ s hs w) :=
  (Commute.one_left _).sub_left ((Commute.one_right _).sub_right
    (translate_commute F μ s hs (globalUniformizerClass F v) (globalUniformizerClass F w)))

theorem globalSobolevPrincipalValue_mapsTo_theta (v : Place F) :
    MapsTo (globalSobolevPrincipalValue F μ s hs v) (N F μ s hs) (N F μ s hs) := by
  intro x hx
  exact (N F μ s hs).sub_mem hx
    (globalThetaSobolevCompletion_mapsTo F μ 0 0 0 s hs (globalUniformizerClass F v) hx)

theorem globalSobolevPrincipalValue_mapsTo_isotype (ω : PontryaginDual (K F)) (v : Place F) :
    MapsTo (globalSobolevPrincipalValue F μ s hs v) (W F μ s hs ω) (W F μ s hs ω) := by
  intro x hx
  let D := globalSobolevPrincipalValue F μ s hs v
  have hx' : ∀ k : K F, translate F μ s hs k.val x = (ω k : ℂ) • x :=
    (mem_thetaCharacterSubspace _ _ _).mp hx
  apply (mem_thetaCharacterSubspace _ _ _).mpr
  intro k
  have hc : Commute (translate F μ s hs k.val) D :=
    (Commute.one_right _).sub_right (translate_commute F μ s hs k.val (globalUniformizerClass F v))
  change translate F μ s hs k.val (D x) = (ω k : ℂ) • D x
  calc
    _ = D (translate F μ s hs k.val x) := DFunLike.congr_fun hc.eq x
    _ = _ := by rw [hx', map_smul]

/-- The zero-line polar-free theta space in the chosen norm-one isotype. -/
def globalOrbitalSobolevIsotype (ω : PontryaginDual (K F)) : Submodule ℂ (Lp ℂ 2 μ) :=
  N F μ s hs ⊓ W F μ s hs ω

theorem globalOrbitalSobolevIsotype_isClosed (ω : PontryaginDual (K F)) :
    IsClosed (globalOrbitalSobolevIsotype F μ s hs ω : Set (Lp ℂ 2 μ)) :=
  (globalThetaSobolevCompletion_isClosed F μ 0 0 0 s hs).inter
    (globalAmbientSobolevIsotype_isClosed F ω μ 0 0 s hs)

/-- Each difference restricts to the completed geometric isotype. -/
def globalIsotypicPrincipalValue (ω : PontryaginDual (K F)) (v : Place F) :
    globalOrbitalSobolevIsotype F μ s hs ω →L[ℂ] globalOrbitalSobolevIsotype F μ s hs ω :=
  ((globalSobolevPrincipalValue F μ s hs v).comp
    (globalOrbitalSobolevIsotype F μ s hs ω).subtypeL).codRestrict _ fun x ↦
      ⟨globalSobolevPrincipalValue_mapsTo_theta F μ s hs v x.property.1,
        globalSobolevPrincipalValue_mapsTo_isotype F μ s hs ω v x.property.2⟩

/-- Identity minus translation by the chosen uniformizer on polar-free theta tests. -/
def globalPolarThetaPrincipalValue (v : Place F) : GlobalPolarTheta F →L[ℂ] GlobalPolarTheta F :=
  1 - globalPolarThetaTranslate F (globalUniformizerClass F v)

theorem globalSobolevPrincipalValue_on_tests (v : Place F) (u : GlobalPolarTheta F) :
    globalSobolevPrincipalValue F μ s hs v (globalThetaSobolevMap F μ 0 0 0 s hs u) =
      globalThetaSobolevMap F μ 0 0 0 s hs (globalPolarThetaPrincipalValue F v u) := by
  simpa [globalSobolevPrincipalValue, globalPolarThetaPrincipalValue, map_sub] using
    congrArg (globalThetaSobolevMap F μ 0 0 0 s hs u - ·)
      (globalThetaSobolevMap_translate F μ 0 0 0 s hs (globalUniformizerClass F v) u)

private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F μ s hs ω

local instance (ω : PontryaginDual (K F)) : CompleteSpace (H F μ s hs ω) :=
  (globalOrbitalSobolevIsotype_isClosed F μ s hs ω).completeSpace_coe

private theorem globalIsotypicPrincipalValue_commute (ω : PontryaginDual (K F)) (v w : Place F) :
    Commute (globalIsotypicPrincipalValue F μ s hs ω v)
      (globalIsotypicPrincipalValue F μ s hs ω w) := by
  ext u : 1
  apply Subtype.ext
  exact DFunLike.congr_fun (globalSobolevPrincipalValue_commute F μ s hs v w).eq u.val

/-- The finite principal-value product acting on the geometric isotype. -/
def globalIsotypicPrincipalValues (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    H F μ s hs ω →L[ℂ] H F μ s hs ω :=
  S.noncommProd (globalIsotypicPrincipalValue F μ s hs ω)
    (fun v _ w _ _ ↦ globalIsotypicPrincipalValue_commute F μ s hs ω v w)

private theorem globalIsotypicPrincipalValues_insert (ω : PontryaginDual (K F))
    (S : Finset (Place F)) (v : Place F) (hv : v ∉ S) :
    globalIsotypicPrincipalValues F μ s hs ω (insert v S) =
      (globalIsotypicPrincipalValues F μ s hs ω S).comp
        (globalIsotypicPrincipalValue F μ s hs ω v) := by
  classical
  unfold globalIsotypicPrincipalValues
  exact Finset.noncommProd_insert_of_notMem' _ _ _ _ hv

/-- The closed range generated by the finite-place differences. -/
def globalClosedPrincipalValueRange (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    ClosedSubmodule ℂ (H F μ s hs ω) where
  toSubmodule := (globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap.range.topologicalClosure
  isClosed' := Submodule.isClosed_topologicalClosure _

theorem globalClosedPrincipalValueRange_antitone (ω : PontryaginDual (K F)) :
    Antitone (globalClosedPrincipalValueRange F μ s hs ω) := by
  classical
  apply Finset.antitone_iff_forall_insert_le.mpr
  intro S v hv
  change (globalIsotypicPrincipalValues F μ s hs ω (insert v S)).toLinearMap.range.topologicalClosure ≤
    (globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap.range.topologicalClosure
  rw [globalIsotypicPrincipalValues_insert F μ s hs ω S v hv]
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨x, rfl⟩
  exact ⟨globalIsotypicPrincipalValue F μ s hs ω v x, rfl⟩

/-- The annihilator in the Hilbert dual is exactly the kernel of the adjoint
of the finite principal-value product. -/
theorem globalClosedPrincipalValueRange_orthogonal (ω : PontryaginDual (K F))
    (S : Finset (Place F)) :
    (globalClosedPrincipalValueRange F μ s hs ω S).toSubmoduleᗮ =
      (globalIsotypicPrincipalValues F μ s hs ω S).adjoint.ker := by
  rw [show (globalClosedPrincipalValueRange F μ s hs ω S).toSubmodule =
    (globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap.range.topologicalClosure from rfl,
    Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonal_range _

private abbrev R (ω : PontryaginDual (K F)) (S : Finset (Place F)) :=
  (globalClosedPrincipalValueRange F μ s hs ω S).toSubmodule

local instance (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    IsClosed (R F μ s hs ω S : Set (H F μ s hs ω)) :=
  (globalClosedPrincipalValueRange F μ s hs ω S).isClosed

/-- The separated orbital quotient is isometric to the adjoint kernel of the
finite principal-value operator. -/
def globalOrbitalQuotientEquiv (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    (H F μ s hs ω ⧸ R F μ s hs ω S) ≃ₗᵢ[ℂ]
      (globalIsotypicPrincipalValues F μ s hs ω S).adjoint.ker :=
  (R F μ s hs ω S).quotientEquivOrthogonal.trans
    (LinearIsometryEquiv.ofEq _ _ (globalClosedPrincipalValueRange_orthogonal F μ s hs ω S))

/-- Abelian Haar convolution commutes with each weighted translation on the
zero line, including translation by a finite-place uniformizer. -/
theorem globalOrbitalConvolution_commutes_translate (φ : C_c(Q F, ℂ)) (g : Q F) :
    Commute (translate F μ s hs g) (globalHardySobolevConvolution F μ 0 0 s hs φ) := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  ext x : 1
  let T := translate F μ s hs
  change T g (∫ h, φ h • T h x ∂μ) = ∫ h, φ h • T h (T g x) ∂μ
  rw [← (T g).integral_comp_comm (integrable_hardySobolev_convolution_orbit μ
    (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs φ x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun h ↦ by
    change T g (φ h • T h x) = φ h • T h (T g x)
    rw [map_smul]
    exact congrArg (φ h • ·) (DFunLike.congr_fun (translate_commute F μ s hs g h).eq x)

/-- Haar convolution on the zero-line geometric isotype. -/
def globalIsotypicOrbitalConvolution (ω : PontryaginDual (K F)) (φ : C_c(Q F, ℂ)) :
    H F μ s hs ω →L[ℂ] H F μ s hs ω :=
  let T := globalHardySobolevConvolution F μ 0 0 s hs φ
  (T.comp (H F μ s hs ω).subtypeL).codRestrict _ fun x ↦
    ⟨globalHardySobolevConvolution_preserves_theta F μ 0 0 0 s hs φ x.property.1,
      globalHardySobolevConvolution_preserves_isotype F ω μ 0 0 s hs φ x.property.2⟩

theorem globalIsotypicOrbitalConvolution_commutes (ω : PontryaginDual (K F))
    (φ : C_c(Q F, ℂ)) (S : Finset (Place F)) :
    Commute (globalIsotypicOrbitalConvolution F μ s hs ω φ)
      (globalIsotypicPrincipalValues F μ s hs ω S) := by
  unfold globalIsotypicPrincipalValues
  refine Finset.noncommProd_induction _ _ _ (fun P ↦ Commute _ P)
    (fun _ _ ha hb ↦ ha.mul_right hb) (Commute.one_right _) ?_
  intro v _
  have hc : Commute (globalHardySobolevConvolution F μ 0 0 s hs φ)
      (globalSobolevPrincipalValue F μ s hs v) :=
    (Commute.one_right _).sub_right
      (globalOrbitalConvolution_commutes_translate F μ s hs φ (globalUniformizerClass F v)).symm
  ext x : 1
  apply Subtype.ext
  exact DFunLike.congr_fun hc.eq x.val

theorem globalIsotypicOrbitalConvolution_preserves_range (ω : PontryaginDual (K F))
    (φ : C_c(Q F, ℂ)) (S : Finset (Place F)) :
    MapsTo (globalIsotypicOrbitalConvolution F μ s hs ω φ) (R F μ s hs ω S) (R F μ s hs ω S) := by
  let A := globalIsotypicOrbitalConvolution F μ s hs ω φ
  let P := globalIsotypicPrincipalValues F μ s hs ω S
  have hmap : MapsTo A (P.toLinearMap.range : Set (H F μ s hs ω)) P.toLinearMap.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨A x, (DFunLike.congr_fun
      (globalIsotypicOrbitalConvolution_commutes F μ s hs ω φ S).eq x).symm⟩
  exact hmap.closure A.continuous

/-- The continuous endomorphism induced by Haar convolution on the
separated orbital Hilbert quotient. -/
def globalOrbitalQuotientConvolution (ω : PontryaginDual (K F))
    (φ : C_c(Q F, ℂ)) (S : Finset (Place F)) :
    (H F μ s hs ω ⧸ R F μ s hs ω S) →L[ℂ] (H F μ s hs ω ⧸ R F μ s hs ω S) :=
  let D := R F μ s hs ω S
  D.liftQL (D.mkQL.comp (globalIsotypicOrbitalConvolution F μ s hs ω φ))
    (fun _ hx ↦ (Submodule.Quotient.mk_eq_zero D).mpr
      (globalIsotypicOrbitalConvolution_preserves_range F μ s hs ω φ S hx))

/-- The orbital quotient is represented in the ambient weighted Hilbert
space by orthogonal representatives. -/
def globalOrbitalRepresentative (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    (R F μ s hs ω S)ᗮ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  (H F μ s hs ω).subtypeₗᵢ.comp (R F μ s hs ω S)ᗮ.subtypeₗᵢ

/-- Orthogonal projection onto the representatives of the separated
orbital quotient in the ambient Hilbert space. -/
def globalOrbitalRepresentativeProjection (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let j := globalOrbitalRepresentative F μ s hs ω S
  let V := j.toLinearMap.range
  letI : IsClosed (V : Set (Lp ℂ 2 μ)) := j.isometry.isClosedEmbedding.isClosed_range
  V.starProjection

/-- At each compact cutoff, the compressed convolution on the orbital
quotient, extended by zero on the ambient orthogonal complement, is trace class. -/
theorem globalOrbital_cutoff_traceClass (ω : PontryaginDual (K F)) (S : Finset (Place F))
    (φ : BruhatSchwartz (Q F)) (hφ : HasCompactSupport φ.val)
    (w : Q F → ℝ) (hw : Measurable w) (hwc : HasCompactSupport w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) :
    let ψ : C_c(Q F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφ⟩
    let P := globalOrbitalRepresentativeProjection F μ s hs ω S
    ∃ T : TraceClass (Lp ℂ 2 μ),
      T.toOperator = P.comp ((cutoffOperator (μ := μ) w hw hw₀ hw₁).comp
        ((globalHardySobolevConvolution F μ 0 0 s hs ψ).comp P)) := by
  intro ψ P
  obtain ⟨A, hA⟩ := globalHardySobolev_cutoff_traceClass F μ 0 0 s hs φ hφ w hw hwc hw₀ hw₁
  refine ⟨TraceClass.leftCompose P (A.rightCompose P), ?_⟩
  change P.comp (A.toOperator.comp P) = _
  rw [hA, ContinuousLinearMap.comp_assoc]

/-- A continuous functional invariant under one selected translation descends
to the separated orbital quotient. -/
theorem globalOrbitalFunctional_descends (ω : PontryaginDual (K F))
    {S : Finset (Place F)} {v : Place F} (hv : v ∈ S)
    (L : Lp ℂ 2 μ →L[ℂ] ℂ)
    (hL : ∀ x, L (translate F μ s hs (globalUniformizerClass F v) x) = L x) :
    ∃ J : (H F μ s hs ω ⧸ R F μ s hs ω S) →L[ℂ] ℂ,
      ∀ x : H F μ s hs ω, J ((R F μ s hs ω S).mkQ x) = L x.val := by
  have hkill (x : H F μ s hs ω) :
      L (globalIsotypicPrincipalValue F μ s hs ω v x).val = 0 := by
    change L (x.val - translate F μ s hs (globalUniformizerClass F v) x.val) = 0
    rw [map_sub, hL, sub_self]
  let M := L.comp (H F μ s hs ω).subtypeL
  let D := (globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap.range
  have hmem : R F μ s hs ω S ≤ M.ker := by
    apply D.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      have he : globalIsotypicPrincipalValues F μ s hs ω S =
          (globalIsotypicPrincipalValue F μ s hs ω v).comp
            (globalIsotypicPrincipalValues F μ s hs ω (S.erase v)) := by
        nth_rewrite 1 [← Finset.insert_erase hv]
        change (insert v (S.erase v)).noncommProd (globalIsotypicPrincipalValue F μ s hs ω) _ = _
        exact Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.notMem_erase _ _)
      change L (globalIsotypicPrincipalValues F μ s hs ω S x).val = 0
      rw [he]
      exact hkill _
    · exact M.isClosed_ker
  exact ⟨(R F μ s hs ω S).liftQL M hmem, fun _ ↦ rfl⟩

/-- The shell space after applying a continuous cutoff and taking the
Hilbert closure. The cutoff can be either shell multiplier from (11.1.2.3). -/
def globalClosedPrincipalValueCutoff (ω : PontryaginDual (K F))
    (C : H F μ s hs ω →L[ℂ] Lp ℂ 2 μ) (S : Finset (Place F)) :
    ClosedSubmodule ℂ (Lp ℂ 2 μ) where
  toSubmodule := ((globalClosedPrincipalValueRange F μ s hs ω S).toSubmodule.map
    C.toLinearMap).topologicalClosure
  isClosed' := Submodule.isClosed_topologicalClosure _

theorem globalClosedPrincipalValueCutoff_antitone (ω : PontryaginDual (K F))
    (C : H F μ s hs ω →L[ℂ] Lp ℂ 2 μ) :
    Antitone (globalClosedPrincipalValueCutoff F μ s hs ω C) :=
  fun _ _ h ↦ Submodule.topologicalClosure_mono (Submodule.map_mono
    (globalClosedPrincipalValueRange_antitone F μ s hs ω h))

/-- Closing before applying the cutoff produces exactly the same final space
as closing the cutoff image of the original operator range. -/
theorem globalClosedPrincipalValueCutoff_eq (ω : PontryaginDual (K F))
    (C : H F μ s hs ω →L[ℂ] Lp ℂ 2 μ) (S : Finset (Place F)) :
    (globalClosedPrincipalValueCutoff F μ s hs ω C S).toSubmodule =
      (C.comp (globalIsotypicPrincipalValues F μ s hs ω S)).toLinearMap.range.topologicalClosure := by
  change ((globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap.range.topologicalClosure.map
    C.toLinearMap).topologicalClosure = _
  let R := (globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap.range
  change (R.topologicalClosure.map C.toLinearMap).topologicalClosure =
    (C.toLinearMap.comp (globalIsotypicPrincipalValues F μ s hs ω S).toLinearMap).range.topologicalClosure
  rw [LinearMap.range_comp]
  apply le_antisymm
  · exact (R.topologicalClosure.map C.toLinearMap).topologicalClosure_minimal (R.topologicalClosure_map C)
      (Submodule.isClosed_topologicalClosure _)
  · exact Submodule.topologicalClosure_mono (Submodule.map_mono R.le_topologicalClosure)

set_option maxHeartbeats 1600000 in
/-- The corrected shell limit is independent of the cofinal sequence of
selected finite places, and convergence holds in the strong operator topology. -/
theorem globalClosedPrincipalValueCutoff_cofinal_tendsto (ω : PontryaginDual (K F))
    (C : H F μ s hs ω →L[ℂ] Lp ℂ 2 μ) (D : Set (Place F))
    (S : ℕ → Finset (Place F)) (hm : Monotone S)
    (hsub : ∀ n, (S n : Set (Place F)) ⊆ D)
    (hcof : ∀ T : Finset (Place F), (T : Set (Place F)) ⊆ D → ∃ n, T ⊆ S n)
    (x : Lp ℂ 2 μ) :
    let P := globalClosedPrincipalValueCutoff F μ s hs ω C
    Tendsto (fun n ↦ (P (S n)).starProjection x) atTop
      (𝓝 ((⨅ T : {T : Finset (Place F) // (T : Set (Place F)) ⊆ D}, P T.val).starProjection x)) := by
  intro P
  have hA := globalClosedPrincipalValueCutoff_antitone F μ s hs ω C
  have h := antitone_starProjection_tendsto (fun n ↦ P (S n)) (hA.comp_monotone hm) x
  have he : (⨅ n, P (S n)) =
      ⨅ T : {T : Finset (Place F) // (T : Set (Place F)) ⊆ D}, P T.val := by
    apply le_antisymm
    · apply le_iInf
      intro T
      obtain ⟨n, hn⟩ := hcof T.val T.property
      exact (iInf_le _ n).trans (hA hn)
    · apply le_iInf
      intro n
      exact iInf_le (fun T : {T : Finset (Place F) // (T : Set (Place F)) ⊆ D} ↦ P T.val)
        ⟨S n, hsub n⟩
  rwa [he] at h

end
end Masullo
