import SLocalOrbitalPolarJets

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- Cauchy's derivative formula as a continuous linear functional of the
boundary values on a fixed circle. -/
def taylorCircleDerivative (c : ℂ) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    C(Metric.sphere c r, ℂ) →L[ℂ] ℂ := by
  letI : CompactSpace (Metric.sphere c r) := isCompact_iff_compactSpace.mp (isCompact_sphere c r)
  let a : C(Metric.sphere c r, ℂ) :=
    ⟨fun w ↦ ((w.val - c)^k)⁻¹,
      ((continuous_subtype_val.sub continuous_const).pow k).inv₀ fun w ↦
        pow_ne_zero _ (sub_ne_zero.mpr fun he ↦ hr.ne' (by
          have hh := Metric.mem_sphere.mp w.property
          simpa [he] using hh.symm))⟩
  let m : C(Metric.sphere c r, ℂ) →L[ℂ] C(Metric.sphere c r, ℂ) :=
    ⟨{ toFun := fun u ↦ a * u
       map_add' := fun u v ↦ mul_add _ _ _
       map_smul' := fun d u ↦ by
         ext w
         simp only [RingHom.id_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
           smul_eq_mul, mul_left_comm] },
      continuous_const.mul continuous_id⟩
  exact (k.factorial : ℂ) • (laurentCircleFunctional c r hr 0).comp m

theorem taylorCircleDerivative_apply (c : ℂ) (r : ℝ) (hr : 0 < r) (k : ℕ)
    (u : C(Metric.sphere c r, ℂ)) (f : ℂ → ℂ)
    (hf : ∀ w : Metric.sphere c r, u w = f w.val)
    (ha : DifferentiableOn ℂ f (Metric.closedBall c r)) :
    taylorCircleDerivative c r hr k u = iteratedDeriv k f c := by
  let a : C(Metric.sphere c r, ℂ) :=
    ⟨fun w ↦ ((w.val - c)^k)⁻¹ * u w,
      ((continuous_subtype_val.sub continuous_const).pow k |>.inv₀ fun w ↦
        pow_ne_zero _ (sub_ne_zero.mpr fun he ↦ hr.ne' (by
          have hh := Metric.mem_sphere.mp w.property
          simpa [he] using hh.symm))).mul u.continuous⟩
  change (k.factorial : ℂ) * laurentCircleFunctional c r hr 0 a = _
  rw [laurentCircleFunctional_apply c r hr 0 a (fun w ↦ ((w - c)^k)⁻¹ * f w)
    (fun w ↦ congrArg (((w.val - c)^k)⁻¹ * ·) (hf w))]
  have hi : EqOn (fun w : ℂ ↦ (w - c)^0 / (w - c) * (((w - c)^k)⁻¹ * f w))
      (fun w ↦ (1 / (w - c)^(k+1)) • f w) (Metric.sphere c r) := by
    intro w hw
    simp only [smul_eq_mul, pow_zero, one_div, pow_succ, mul_inv]
    ring
  rw [circleIntegral.integral_congr hr.le hi, ha.circleIntegral_one_div_sub_center_pow_smul hr]
  rw [smul_eq_mul]
  field_simp [Complex.two_pi_I_ne_zero, Nat.factorial_ne_zero]

variable (F : Type*) [Field F] [NumberField F]
private abbrev P := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F

variable (S : Finset (P F))
private abbrev K := SLocalThetaNormOne F S

private theorem sLocalMellinRegularSet_mem_right (χ : PontryaginDual (K F S))
    {w : ℂ} (hw : 0 < w.re) : w ∈ sLocalMellinRegularSet F S χ := by
  refine ⟨?_, ?_, sLocalFiniteZetaDenominator_ne_zero_of_pos F S _ w hw⟩
  · intro i k he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, sLocalRealArchParameters_re, add_zero, Complex.natCast_re,
      Complex.zero_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  · intro i k he
    have hh := congrArg Complex.re he
    simp [Complex.mul_re, sLocalComplexArchParameters_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable [∀ v : P F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : P F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : P F, Measure (v.adicCompletion F)ˣ)
  [∀ v : P F, (μ v).IsHaarMeasure] [∀ v : P F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hν : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F))
    Measure.count (sLocalClassHaar F S ν))

private abbrev Z (χ : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S (fun v ↦ μ v.val) χ
    (sLocalRealArchParameters F S χ) (sLocalComplexArchParameters F S χ) f

include hν in
set_option maxHeartbeats 850000 in
/-- Every reflected derivative is a continuous linear functional of the
test. There is no restriction on its order, including at the polar jet. -/
theorem exists_sLocalOrbitalCompressedJetCLM (χ : PontryaginDual (K F S))
    (c : ℂ) (hc : c.re = 0) (k : ℕ) :
    ∃ L : E F S →L[ℂ] ℂ, ∀ f, L f =
      iteratedDeriv k (fun z ↦ Z F S μ χ (sLocalFourierCompression F S f) (1-z)) c := by
  let w := 1 - c
  let r : ℝ := 1/2
  have hr : 0 < r := by norm_num [r]
  let C := Metric.sphere w r
  have hRight : Metric.closedBall w r ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hd : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hRe := Complex.abs_re_le_norm (z-w)
    rw [Complex.sub_re, show w.re = 1 by simp [w, hc]] at hRe
    have h : |z.re - 1| ≤ (1 : ℝ) / 2 := hRe.trans hd
    change 0 < z.re
    linarith [(abs_le.mp h).1]
  have hC : IsCompact C := isCompact_sphere _ _
  have hReg : C ⊆ sLocalMellinRegularSet F S χ :=
    fun z hz ↦ sLocalMellinRegularSet_mem_right F S χ (hRight (Metric.sphere_subset_closedBall hz))
  let L := (taylorCircleDerivative w r hr k).comp
    ((sLocalMellinCompact F S (fun v ↦ μ v.val) χ C hC hReg).comp (sLocalFourierCompression F S))
  refine ⟨(-1 : ℂ)^k • L, fun f ↦ ?_⟩
  let g := sLocalFourierCompression F S f
  have hA : DifferentiableOn ℂ (Z F S μ χ g) (Metric.closedBall w r) := by
    intro z hz
    have hp := hRight hz
    have he : Z F S μ χ g =ᶠ[𝓝 z] sLocalThetaZetaIntegral F S ν χ g := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp] with y hy
      exact sLocalContinuedZeta_eq_theta F S (fun v ↦ μ v.val) ν hν χ g hy
    exact ((sLocalThetaZeta_analytic F S ν χ g z hp).congr he.symm).differentiableAt.differentiableWithinAt
  change (-1 : ℂ)^k •
    taylorCircleDerivative w r hr k (sLocalMellinCompact F S (fun v ↦ μ v.val) χ C hC hReg g) = _
  rw [taylorCircleDerivative_apply w r hr k _ (Z F S μ χ g) (fun _ ↦ rfl) hA,
    iteratedDeriv_comp_const_sub]


local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
  (hνG : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
variable (ω : PontryaginDual (normOneIdeleClass F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev A := sLocalNormOneCharacterOfGlobal F ω S hs hu

include hν hνG in
/-- All reflected derivatives descend continuously to the homogeneous
quotient before imposing any principal-value relations. -/
theorem exists_sLocalOrbitalCompressedJet_homogeneousCLM
    (c : ℂ) (hc : c.re = 0) (k : ℕ) :
    let χ := A F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S ν χ
    ∃ L : (SLocalHomogeneousThetaQuotient F S ν χ) →L[ℂ] ℂ, ∀ f, L (M.mkQ f) =
      iteratedDeriv k (fun z ↦ Z F S μ χ⁻¹ (sLocalFourierCompression F S f) (1-z)) c := by
  intro χ M
  obtain ⟨L, hL⟩ := exists_sLocalOrbitalCompressedJetCLM F S μ ν hν χ⁻¹ c hc k
  have hker : M ≤ L.ker := by
    intro f hf
    have hθ := (mem_sLocalHomogeneousThetaKernel_iff F S ν χ f).mp hf
    have hz := (sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S (fun v ↦ μ v.val)
      ν hν χ f).mp hθ
    change Submodule.Quotient.mk (p := zeroMeromorphicGerms)
      (⟨Z F S μ χ f, sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) χ _ _ f⟩ :
        meromorphicRepresentatives) = 0 at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    have he : Z F S μ χ f =ᶠ[𝓝[≠] c] 0 := hz c
    have hn : sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) χ f =ᶠ[𝓝[≠] c] 0 := by
      filter_upwards [he, sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) χ f c]
        with z hz' hg
      change Z F S μ χ f z = 0 at hz'
      rw [hg]
      change sLocalEulerDenominator F S χ z * Z F S μ χ f z = 0
      rw [hz', mul_zero]
    have ho := meromorphicOrderAt_eq_top_iff.mpr hn
    have h := (sLocalOrbitalCompressedJet_vanish_iff_normalized_order F S μ η νG hνG ω hs hu
      ν hν f c hc (k + 1)).mpr (ho ▸ le_top) k (Nat.lt_succ_self k)
    exact LinearMap.mem_ker.mpr ((hL f).trans h)
  exact ⟨M.liftQL L hker, hL⟩

include hν hνG in
/-- The true two-moment principal-value range is closed. The full family
of continuous reflected jets includes the enhanced trivial-character
coordinate at zero. -/
theorem isClosed_sLocalPaleyWienerOrbitalRange
    (W : Finset S)
    (hW : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S (A F S ω hs hu) v)) :
    IsClosed (sLocalPaleyWienerOrbitalRange F ν (A F S ω hs hu) W :
      Set (sLocalPaleyWienerMomentImage F ν (A F S ω hs hu))) := by
  let χ := A F S ω hs hu
  let M := sLocalHomogeneousThetaKernel F S ν χ
  let H := sLocalPaleyWienerMomentImage F ν χ
  let R := sLocalPaleyWienerOrbitalRange F ν χ W
  let n (c : ℂ) := sLocalSelectedFinitePoleCount F S χ W c + (if ω = 1 ∧ c = 0 then 1 else 0)
  let I := {j : ℂ × ℕ // j.1.re = 0 ∧ j.2 < n j.1}
  choose J hJ using fun j : I ↦ exists_sLocalOrbitalCompressedJet_homogeneousCLM
    F S μ ν hν η νG hνG ω hs hu j.val.1 j.property.1 j.val.2
  have he : (R : Set H) = ⋂ j : I, {q | J j q.val = 0} := by
    ext q
    obtain ⟨f, hf, hq⟩ := Submodule.mem_map.mp q.property
    let q' : H := ⟨M.mkQ f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩
    have hEq : q' = q := Subtype.ext hq
    subst q
    let eq := sLocalPaleyWienerOrbitalClass_eq_zero_iff_polarJets F S νG μ η hνG ω hs hu
      ν hν W hW f hf
    change q' ∈ R ↔ q' ∈ ⋂ j : I, {q : H | J j q.val = 0}
    refine (Submodule.Quotient.mk_eq_zero R).symm.trans ?_
    rw [Set.mem_iInter]
    constructor
    · intro h j
      have hjet := eq.mp h j.val.1 j.property.1 j.val.2 j.property.2
      exact (hJ j f).trans hjet
    · intro h
      apply eq.mpr
      intro c hc k hk
      let j : I := ⟨(c,k), hc,hk⟩
      exact (hJ j f).symm.trans (h j)
  change IsClosed (R : Set H)
  rw [he]
  exact isClosed_iInter fun j ↦ isClosed_eq ((J j).continuous.comp continuous_subtype_val) continuous_const

include hν hνG in
/-- The intersection denominator in the proof of Theorem 7.3.3.4 is
closed at every fixed absolute or invariant level. -/
theorem isClosed_sLocalPaleyWienerLevel_intersection {B : Finset (P F)}
    (hBS : B ⊆ S) (K₀ : Set (SAdeles F B)) (W : Finset S)
    (hW : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S (A F S ω hs hu) v)) :
    let χ := A F S ω hs hu
    let L := sLocalPaleyWienerMomentLevelInclusion F ν χ hBS K₀
    IsClosed ((sLocalPaleyWienerOrbitalRange F ν χ W).comap L.toLinearMap :
      Set (sLocalPaleyWienerThetaLevel F S ν χ hBS K₀ (sLocalPaleyWienerMomentKernel F S))) :=
  (isClosed_sLocalPaleyWienerOrbitalRange F S μ ν hν η νG hνG ω hs hu W hW).preimage
    (sLocalPaleyWienerMomentLevelInclusion F ν (A F S ω hs hu) hBS K₀).continuous

include hν hνG in
/-- The fixed-level quotients defined with the intersection denominator
are Hausdorff for their original quotient topology. -/
theorem t2Space_sLocalPaleyWienerLevel_intersection {B : Finset (P F)}
    (hBS : B ⊆ S) (K₀ : Set (SAdeles F B)) (W : Finset S)
    (hW : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S (A F S ω hs hu) v)) :
    let χ := A F S ω hs hu
    let V := sLocalPaleyWienerThetaLevel F S ν χ hBS K₀ (sLocalPaleyWienerMomentKernel F S)
    let L := sLocalPaleyWienerMomentLevelInclusion F ν χ hBS K₀
    T2Space (V ⧸ (sLocalPaleyWienerOrbitalRange F ν χ W).comap L.toLinearMap) := by
  intro χ V L
  let R := (sLocalPaleyWienerOrbitalRange F ν χ W).comap L.toLinearMap
  have hClosed : IsClosed (R : Set V) :=
    isClosed_sLocalPaleyWienerLevel_intersection F S μ ν hν η νG hνG ω hs hu hBS K₀ W hW
  change T2Space (V ⧸ R)
  apply IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr
  apply R.isQuotientMap_mkQL.isClosed_preimage.mp
  convert hClosed using 1
  ext x
  exact Submodule.Quotient.mk_eq_zero R

include hν hνG in
/-- The corrected coordinates, including the extra coordinate at zero,
are continuous linear functionals on the two-moment orbital quotient. -/
theorem exists_sLocalPaleyWienerOrbitalJetCLM
    (W : Finset S)
    (hW : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S (A F S ω hs hu) v))
    (c : ℂ) (hc : c.re = 0) (k : ℕ)
    (hk : k < sLocalSelectedFinitePoleCount F S (A F S ω hs hu) W c +
      (if ω = 1 ∧ c = 0 then 1 else 0)) :
    let χ := A F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S ν χ
    let H := sLocalPaleyWienerMomentImage F ν χ
    let R := sLocalPaleyWienerOrbitalRange F ν χ W
    ∃ L : (H ⧸ R) →L[ℂ] ℂ,
      ∀ (f : E F S) (hf : GlobalBruhat.polarEvaluation F f.val = 0),
        L (R.mkQ ⟨M.mkQ f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩) =
          iteratedDeriv k (fun z ↦ Z F S μ χ⁻¹ (sLocalFourierCompression F S f) (1-z)) c := by
  intro χ M H R
  obtain ⟨L, hL⟩ := exists_sLocalOrbitalCompressedJet_homogeneousCLM F S μ ν hν η νG hνG
    ω hs hu c hc k
  let J := L.comp H.subtypeL
  have hJ : R ≤ J.ker := by
    intro q hq
    obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp q.property
    let q' : H := ⟨M.mkQ f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩
    have hEq : q' = q := Subtype.ext he
    subst q
    have hZero : R.mkQ q' = 0 := (Submodule.Quotient.mk_eq_zero R).mpr hq
    have hJet := (sLocalPaleyWienerOrbitalClass_eq_zero_iff_polarJets F S νG μ η hνG
      ω hs hu ν hν W hW f hf).mp hZero c hc k hk
    exact LinearMap.mem_ker.mpr ((hL f).trans hJet)
  exact ⟨R.liftQL J hJ, fun f _ ↦ hL f⟩

end

end Masullo
