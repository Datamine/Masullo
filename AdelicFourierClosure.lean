import AdelicPoisson
import AdelicDerivatives
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.Complex

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField RestrictedProduct SchwartzMap FourierTransform InnerProductSpace

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev A := Adeles F
private abbrev V := mixedEmbedding.mixedSpace F
private abbrev K := FiniteAdeleRing (𝓞 F) F

local instance adelicFourierClosureMeasurableAdeles : MeasurableSpace (A F) := borel _
local instance adelicFourierClosureBorelAdeles : BorelSpace (A F) := ⟨rfl⟩
local instance adelicFourierClosureMeasurableFiniteAdeles : MeasurableSpace (K F) := borel _
local instance adelicFourierClosureBorelFiniteAdeles : BorelSpace (K F) := ⟨rfl⟩
local instance adelicFourierClosureLocallyCompactFiniteAdeles : LocallyCompactSpace (K F) := finiteAdeles_locallyCompact
local instance adelicFourierClosureLocallyCompactAdeles : LocallyCompactSpace (A F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × K F))
local instance adelicFourierClosureSecondCountableAdeles : SecondCountableTopology (A F) := adeles_secondCountable F
local instance adelicFourierClosureSecondCountableFiniteAdeles : SecondCountableTopology (K F) := finiteAdeles_secondCountable F
local instance adelicFourierClosureHausdorffFiniteAdeles : T2Space (K F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))
local instance adelicFourierClosureHausdorffAdeles : T2Space (A F) := by
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × K F))

private def mixedAdeleChart : V F × K F ≃ₜ+ A F where
  toHomeomorph := (infiniteAdeleMixedHomeomorph F).symm.prodCongr (Homeomorph.refl _)
  map_add' x y := by
    apply Prod.ext
    · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _
    · rfl

/-- The adele with the given mixed archimedean component and finite component zero. -/
def archAdele (x : V F) : A F := (mixedAdeleChart F) (x, 0)

private theorem adelicHaarUnitDomain_eq_mixedProduct (ν : Measure (K F)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, adelicHaarUnitDomain F =
      c • ((volume : Measure (V F)).prod ν).map (mixedAdeleChart F) := by
  let e := mixedAdeleChart F
  let μ := (volume : Measure (V F)).prod ν
  let μ' : Measure (A F) := μ.map e
  letI : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  letI : μ'.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul (adelicHaarUnitDomain F) μ'⟩

/-- The Fourier transform of a pure adelic tensor factors into its
archimedean and finite Fourier integrals, with the Haar normalization scalar. -/
theorem adelicFourier_bruhatTensor_factor (ν : Measure (K F)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, ∀ (φ : 𝓢(V F, ℂ)) (ψ : FiniteBruhat F) (ξ : A F),
      adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (bruhatTensor F φ ψ) ξ =
      (c : ℝ) •
        ((∫ x : V F, φ x *
          ((standardAdelicCharacter F (archAdele F x * ξ)).toMul : ℂ)) *
         (∫ y : K F, ψ.toLocallyConstant y *
          ((standardAdelicCharacter F (finiteAdelicTranslation F y * ξ)).toMul : ℂ) ∂ν)) := by
  let e := mixedAdeleChart F
  let μ := (volume : Measure (V F)).prod ν
  obtain ⟨c, hm⟩ := adelicHaarUnitDomain_eq_mixedProduct F ν
  refine ⟨c, fun φ ψ ξ => ?_⟩
  let χ := standardAdelicCharacter F
  let q (a : A F) := bruhatTensor F φ ψ a * ((χ (a * ξ)).toMul : ℂ)
  change (∫ a, q a ∂adelicHaarUnitDomain F) = _
  rw [hm, integral_smul_nnreal_measure]
  congr 1
  let d : V F × K F ≃ᵐ A F := e.toHomeomorph.toMeasurableEquiv
  change ∫ a, q a ∂μ.map d = _
  rw [integral_map_equiv]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  refine .of_forall fun p => ?_
  have hp : e p = archAdele F p.1 + finiteAdelicTranslation F p.2 := by
    apply Prod.ext
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  have htest : bruhatTensor F φ ψ (e p) = φ p.1 * ψ.toLocallyConstant p.2 := by
    change φ ((InfiniteAdeleRing.ringEquiv_mixedSpace F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p.1)) * ψ.toLocallyConstant p.2 = _
    rw [RingEquiv.apply_symm_apply]
  change bruhatTensor F φ ψ (e p) * ((χ (e p * ξ)).toMul : ℂ) = _
  rw [htest, hp, add_mul, map_add]
  change (φ p.1 * ψ.toLocallyConstant p.2) *
    (((χ (archAdele F p.1 * ξ)).toMul * (χ (finiteAdelicTranslation F p.2 * ξ)).toMul : Circle) : ℂ) = _
  rw [Circle.coe_mul]
  ring

private def finiteAdelicCharacter : K F →+ Additive Circle :=
  (standardAdelicCharacter F).comp {
    toFun := finiteAdelicTranslation F
    map_zero' := rfl
    map_add' x y := by
      apply Prod.ext
      · exact (zero_add _).symm
      · rfl }

/-- The finite factor of the additive Fourier integral. -/
def finiteAdelicFourier (ν : Measure (K F)) (ψ : K F → ℂ) (y : K F) : ℂ :=
  ∫ x, ψ x * ((finiteAdelicCharacter F (x * y)).toMul : ℂ) ∂ν

set_option maxHeartbeats 1000000 in
theorem finiteAdelicFourier_isLocallyConstant (ν : Measure (K F)) (ψ : FiniteBruhat F) :
    IsLocallyConstant (finiteAdelicFourier F ν ψ.toLocallyConstant) := by
  let f := ψ.toLocallyConstant
  let χ := finiteAdelicCharacter F
  let C : Set (K F) := tsupport f
  have hC : IsCompact C := ψ.compactSupport
  let E : Set (K F × K F) := {p | χ (p.1 * p.2) = 0}
  have hE : IsOpen E := (standardAdelicCharacter_finite_kernel_open F).preimage
    (continuous_fst.mul continuous_snd)
  obtain ⟨U, W, -, hW, hU, h0, hUW⟩ := generalized_tube_lemma hC
    (isCompact_singleton (x := (0 : K F))) hE (by
      rintro ⟨x, u⟩ ⟨_, hu⟩
      have he : u = 0 := mem_singleton_iff.mp hu
      simp [E, he])
  have hpair (x u : K F) (hx : x ∈ C) (hu : u ∈ W) : χ (x * u) = 0 := by
    have hp : (x, u) ∈ U ×ˢ W := ⟨hU hx, hu⟩
    change (x, u) ∈ E
    exact hUW hp
  have hfix (y u : K F) (hu : u ∈ W) :
      finiteAdelicFourier F ν f (y + u) = finiteAdelicFourier F ν f y := by
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    change f x * ((χ (x * (y + u))).toMul : ℂ) = f x * ((χ (x * y)).toMul : ℂ)
    by_cases hx : x ∈ C
    · rw [mul_add, map_add, hpair x u hx hu, add_zero]
    · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [hzero, zero_mul]
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  have hW' : ∀ᶠ z in 𝓝 y, z - y ∈ W :=
    (hW.preimage (continuous_id.sub continuous_const)).mem_nhds (by
      change y - y ∈ W
      rw [sub_self]
      exact h0 (by simp))
  filter_upwards [hW'] with z hz
  simpa only [add_sub_cancel] using hfix y (z - y) hz

private theorem finiteAdelicFourier_eq_zero_of_translation
    (ν : Measure (K F)) [ν.IsAddHaarMeasure] {f : K F → ℂ}
    (u : K F) (hu : ∀ x, f (x + u) = f x) (y : K F)
    (h : finiteAdelicCharacter F (u * y) ≠ 0) : finiteAdelicFourier F ν f y = 0 := by
  let χ := finiteAdelicCharacter F
  let w (x : K F) := f x * ((χ (x * y)).toMul : ℂ)
  let c : ℂ := (χ (u * y)).toMul
  have htrans (x : K F) : w (x + u) = w x * c := by
    change f (x + u) * ((χ ((x + u) * y)).toMul : ℂ) = _
    rw [hu, add_mul, map_add]
    change f x * (((χ (x * y)).toMul * (χ (u * y)).toMul : Circle) : ℂ) = w x * c
    rw [Circle.coe_mul, ← mul_assoc]
  have he : (∫ a, w a ∂ν) = (∫ a, w a ∂ν) * c := by
    rw [← integral_mul_const, ← integral_add_right_eq_self w u]
    exact integral_congr_ae (.of_forall htrans)
  have hc : c ≠ 1 := by
    intro hc
    apply h
    apply Additive.toMul.injective
    change (χ (u * y)).toMul = (1 : Circle)
    apply Subtype.ext
    exact hc
  exact (mul_eq_mul_left_iff.mp ((mul_one _).trans he)).resolve_left (by simpa [ne_comm] using hc)

/-- The Fourier transform of a finite Schwartz–Bruhat test has compact
support. In trace coordinates its support lies in a product of compact
dilates of the integral rational finite adeles. -/
theorem finiteAdelicFourier_hasCompactSupport (ν : Measure (K F)) [ν.IsAddHaarMeasure]
    (ψ : FiniteBruhat F) : HasCompactSupport (finiteAdelicFourier F ν ψ.toLocallyConstant) := by
  obtain ⟨n, hn, hnU⟩ := finiteIntegralAdeles_nat_mul_subset_nhds F (finiteBruhat_stabilizer_nhds F ψ)
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let R := K ℚ
  let b := integralBasis F
  let j := algebraMap F (A F)
  let d := algebraMap F (K F)
  let a (y : K F) := finiteAdelicTranslation F y
  let τ (y : K F) (i : J) :=
    (relativeAdelicTraceRat F (a y * j (b i))).2
  let q := algebraMap ℚ R ((n : ℚ)⁻¹)
  let D : Set R := (fun z : R => q * z) '' (finiteIntegralAdeles ℚ : Set R)
  have hD : IsCompact D := (isCompact_finiteIntegralAdeles ℚ).image
    (continuous_const.mul continuous_id)
  let L (z : J → R) : K F :=
    ∑ i, finiteAdelesExtension ℚ F (z i) * d (b.traceDual i)
  have hL : Continuous L := continuous_finsetSum _ fun i _ =>
    ((finiteAdelesExtension_continuous ℚ F).comp (continuous_apply i)).mul continuous_const
  have hcompact : IsCompact (L '' (univ.pi fun _ : J => D)) :=
    (isCompact_univ_pi fun _ : J => hD).image hL
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  intro y hy
  have htr (i : J) : (n : R) * τ y i ∈ finiteIntegralAdeles ℚ := by
    have hbi : d (b i) ∈ finiteIntegralAdeles F :=
      (finiteDiagonal_mem_integral F _).mpr
        ⟨RingOfIntegers.basis F i, (integralBasis_apply F i).symm⟩
    let u := (n : K F) * d (b i)
    have hu : ∀ x, ψ.toLocallyConstant (x + u) = ψ.toLocallyConstant x :=
      hnU ⟨d (b i), hbi, rfl⟩
    have hχ : finiteAdelicCharacter F (u * y) = 0 := by
      by_contra hne
      exact hy (finiteAdelicFourier_eq_zero_of_translation F ν u hu y hne)
    have hz := (standardAdelicCharacter_finite_eq_zero_iff F (u * y)).mp hχ
    have he : a (u * y) = n • (a y * j (b i)) := by
      apply Prod.ext
      · change 0 = n • (0 * (j (b i)).1)
        rw [zero_mul, smul_zero]
      · change ((n : K F) * d (b i)) * y = n • (y * d (b i))
        rw [nsmul_eq_mul]
        ac_rfl
    change (relativeAdelicTraceRat F (a (u * y))).2 ∈ _ at hz
    rw [he, map_nsmul] at hz
    change n • τ y i ∈ _ at hz
    rwa [nsmul_eq_mul] at hz
  have hcoords (i : J) : τ y i ∈ D := by
    refine ⟨(n : R) * τ y i, htr i, ?_⟩
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    change ((algebraMap ℚ R) ((n : ℚ)⁻¹)) * ((n : R) * τ y i) = _
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hn', map_one, one_mul]
  refine ⟨τ y, mem_univ_pi.mpr hcoords, ?_⟩
  let π : A F →+* K F := RingHom.snd _ _
  have he := congrArg π (relativeAdelicTraceRat_sum_traceDual F (a y))
  rw [map_sum] at he
  exact he

private theorem archAdele_add (x y : V F) :
    archAdele F (x + y) = archAdele F x + archAdele F y := by
  apply Prod.ext
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _
  · exact (zero_add _).symm

private theorem archAdele_mul (x y : V F) :
    archAdele F (x * y) = archAdele F x * archAdele F y := by
  apply Prod.ext
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_mul _ _
  · exact (zero_mul _).symm

private theorem archAdele_continuous : Continuous (archAdele F) :=
  (mixedAdeleChart F).continuous.comp (continuous_id.prodMk continuous_const)

private theorem relativeAdelicTraceRat_arch_snd (x : V F) :
    (relativeAdelicTraceRat F (archAdele F x)).2 = 0 := by
  let e : Adeles ℚ := (1, 0)
  let a := archAdele F x
  have he : adelesExtension ℚ F e * a = a := by
    apply Prod.ext
    · change infiniteAdelesExtension ℚ F 1 * a.1 = a.1
      rw [map_one, one_mul]
    · change finiteAdelesExtension ℚ F 0 * a.2 = a.2
      rw [map_zero, zero_mul]
      rfl
  have h := relativeAdelicTraceRat_mul_rat F e a
  rw [he] at h
  exact (congrArg Prod.snd h).trans (zero_mul _)

private def archTraceValue (x : V F) : ℝ :=
  rationalArchCoordinate (relativeAdelicTraceRat F (archAdele F x)).1

private theorem archTraceValue_continuous : Continuous (archTraceValue F) :=
  rationalArchCoordinate_continuous.comp (continuous_fst.comp
    ((relativeAdelicTraceRat_continuous F).comp (archAdele_continuous F)))

private theorem archAdele_rat_smul (q : ℚ) (x : V F) :
    archAdele F ((q : ℝ) • x) =
      adelesExtension ℚ F (algebraMap ℚ (A ℚ) q) * archAdele F x := by
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  rw [adelesExtension_diagonal]
  apply Prod.ext
  · apply m.injective
    change m (m.symm ((q : ℝ) • x)) =
      m ((algebraMap F (InfiniteAdeleRing F) (algebraMap ℚ F q)) * m.symm x)
    rw [map_mul, m.apply_symm_apply, m.apply_symm_apply]
    have h := DFunLike.congr_fun (Subsingleton.elim
      (m.toRingHom.comp ((algebraMap F (InfiniteAdeleRing F)).comp (algebraMap ℚ F)))
      ((algebraMap ℝ (V F)).comp (algebraMap ℚ ℝ))) q
    change m (algebraMap F (InfiniteAdeleRing F) (algebraMap ℚ F q)) =
      algebraMap ℝ (V F) (q : ℝ) at h
    rw [h, Algebra.smul_def]
  · exact (mul_zero _).symm

/-- The real-linear archimedean component of the relative adelic trace. -/
def adelicArchTrace : V F →L[ℝ] ℝ where
  toLinearMap :=
    { toFun := archTraceValue F
      map_add' x y := by
        unfold archTraceValue
        rw [archAdele_add, map_add]
        exact (rationalArchCoordinate.map_add _ _)
      map_smul' r x := by
        change archTraceValue F (r • x) = r * archTraceValue F x
        exact congrFun ((Rat.denseRange_cast (𝕜 := ℝ)).equalizer
          ((archTraceValue_continuous F).comp (continuous_id.smul continuous_const))
          (continuous_id.mul continuous_const) (funext fun q => by
            change archTraceValue F ((q : ℝ) • x) = (q : ℝ) * archTraceValue F x
            unfold archTraceValue
            rw [archAdele_rat_smul F q, relativeAdelicTraceRat_mul_rat]
            change rationalArchCoordinate ((algebraMap ℚ (A ℚ) q).1 *
              (relativeAdelicTraceRat F (archAdele F x)).1) = _
            rw [map_mul, rationalArchCoordinate_diag])) r }
  cont := archTraceValue_continuous F

private theorem adelicArchTrace_diagonal (x : F) :
    adelicArchTrace F (mixedEmbedding F x) = (Algebra.trace ℚ F x : ℝ) := by
  let e : Adeles ℚ := (1, 0)
  let j : F →+* A F := algebraMap F (A F)
  have he : archAdele F (mixedEmbedding F x) = adelesExtension ℚ F e * j x := by
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedEmbedding F x) =
        infiniteAdelesExtension ℚ F 1 * (algebraMap F (InfiniteAdeleRing F) x)
      rw [map_one, one_mul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F]
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
    · change 0 = finiteAdelesExtension ℚ F 0 * _
      rw [map_zero, zero_mul]
  change rationalArchCoordinate (relativeAdelicTraceRat F (archAdele F (mixedEmbedding F x))).1 = _
  rw [he, relativeAdelicTraceRat_mul_rat, relativeAdelicTraceRat_diagonal]
  change rationalArchCoordinate (1 * (algebraMap ℚ (Adeles ℚ) _).1) = _
  rw [one_mul, rationalArchCoordinate_diag]

private theorem mixedSpace_trace_diagonal (x : F) :
    Algebra.trace ℝ (V F) (mixedEmbedding F x) = (Algebra.trace ℚ F x : ℝ) := by
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.latticeBasis F),
    Algebra.trace_eq_matrix_trace (integralBasis F)]
  simp only [Matrix.trace, Matrix.diag, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    mixedEmbedding.latticeBasis_apply, ← map_mul, mixedEmbedding.latticeBasis_repr_apply]

private theorem trace_pi_coordinates {ι B : Type*} [Fintype ι] [CommRing B] [Algebra ℝ B]
    {κ : Type*} [Fintype κ] (b : Module.Basis κ ℝ B) (x : ι → B) :
    Algebra.trace ℝ (ι → B) x = ∑ i, Algebra.trace ℝ B (x i) := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι ↦ b)]
  simp only [Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.diag,
    Finset.univ_sigma_univ, Finset.sum_sigma']
  apply Finset.sum_congr rfl
  rintro ⟨i,k⟩ _
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Pi.basis_repr, Pi.basis_apply, Pi.mul_apply, Pi.single_eq_same]

/-- The adelic archimedean character uses the ordinary real trace at
real places and twice the real part at complex places. -/
theorem adelicArchTrace_eq_sum_places (x : V F) :
    adelicArchTrace F x =
      (∑ v : {w : InfinitePlace F // w.IsReal}, x.1 v) +
        ∑ v : {w : InfinitePlace F // w.IsComplex}, 2 * (x.2 v).re := by
  have h : (adelicArchTrace F).toLinearMap = Algebra.trace ℝ (V F) := by
    apply (mixedEmbedding.latticeBasis F).ext
    intro i
    rw [mixedEmbedding.latticeBasis_apply]
    exact (adelicArchTrace_diagonal F _).trans (mixedSpace_trace_diagonal F _).symm
  change (adelicArchTrace F).toLinearMap x = _
  rw [h, Algebra.trace_prod_apply,
    trace_pi_coordinates (Module.Basis.singleton Unit ℝ),
    trace_pi_coordinates Complex.basisOneI]
  simp only [Algebra.trace_complex_apply, Algebra.trace_self_apply]

theorem standardAdelicCharacter_arch (x : V F) :
    (standardAdelicCharacter F (archAdele F x)).toMul =
      Circle.exp (2 * Real.pi * adelicArchTrace F x) := by
  exact congrArg Additive.toMul (rationalAdelicCharacter_apply_of_zero_finite _
    (relativeAdelicTraceRat_arch_snd F x))

/-- An archimedean first moment of a Schwartz–Bruhat test is integrable. -/
theorem bruhat_mixedArch_norm_integrable {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Integrable (fun a => ‖mixedArch a‖ * ‖f a‖) (adelicHaarUnitDomain F) := by
  let μ := adelicHaarUnitDomain F
  let p (f : A F → ℂ) (a : A F) := ‖mixedArch a‖ * ‖f a‖
  have hp {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F) : Continuous (p f) :=
    (infiniteAdele_toMixed_continuous F |>.comp continuous_fst).norm.mul
      (bruhat_continuous F hf).norm
  change Integrable (p f) μ
  apply Submodule.span_induction (p := fun f _ => Integrable (p f) μ) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    let ν := Measure.addHaar (G := K F)
    obtain ⟨c, hc⟩ := adelicHaarUnitDomain_eq_mixedProduct F ν
    change Integrable _ (adelicHaarUnitDomain F)
    rw [hc]
    apply Integrable.smul_measure_nnreal
    let e := (mixedAdeleChart F).toHomeomorph.toMeasurableEquiv
    apply (integrable_map_equiv e _).mpr
    have hφ : Integrable (fun x : V F => ‖x‖ * ‖φ x‖) volume := by
      simpa only [pow_one] using φ.integrable_pow_mul volume 1
    have hψ : Integrable (fun y : K F => ‖ψ.toLocallyConstant y‖) ν :=
      ψ.toLocallyConstant.continuous.norm.integrable_of_hasCompactSupport
        (ψ.compactSupport.comp_left norm_zero)
    refine (hφ.mul_prod hψ).congr (.of_forall fun z => ?_)
    change (‖z.1‖ * ‖φ z.1‖) * ‖ψ.toLocallyConstant z.2‖ =
      ‖mixedArch (mixedAdeleChart F z)‖ * ‖φ (mixedArch (mixedAdeleChart F z)) * ψ.toLocallyConstant z.2‖
    have hz : mixedArch (mixedAdeleChart F z) = z.1 :=
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z.1
    rw [hz, norm_mul, mul_assoc]
  · simp [p]
  · intro f g hf hg hfi hgi
    apply (hfi.add hgi).mono' (hp ((bruhatSubmodule F).add_mem hf hg)).aestronglyMeasurable
    exact .of_forall fun x => by
      rw [Real.norm_of_nonneg (by dsimp [p]; positivity)]
      simp only [p, Pi.add_apply, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  · intro c f _ hi
    have he : p (c • f) = fun a => ‖c‖ * p f a := by
      funext a
      simp only [p, Pi.smul_apply, norm_smul]
      ring
    rw [he]
    exact hi.const_mul _

theorem archAdele_mul_adele (x : V F) (ξ : A F) :
    archAdele F x * ξ = archAdele F (x * mixedArch ξ) := by
  apply Prod.ext
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x * ξ.1 =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (x * (InfiniteAdeleRing.ringEquiv_mixedSpace F) ξ.1)
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact zero_mul _

private abbrev ArchIndex := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
private abbrev Euclidean := EuclideanSpace ℝ (ArchIndex F)

private def archLebesgueChart : Euclidean F ≃L[ℝ] V F :=
  ((WithLp.linearEquiv 2 ℝ (ArchIndex F → ℝ)).trans
    (mixedEmbedding.latticeBasis F).equivFun.symm).toContinuousLinearEquiv

private def archFrequencyMap : V F →ₗ[ℝ] Euclidean F :=
  (WithLp.linearEquiv 2 ℝ (ArchIndex F → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun i =>
      (adelicArchTrace F).toLinearMap.comp (Algebra.lmul ℝ (V F) (mixedEmbedding.latticeBasis F i)))

private theorem archFrequencyMap_apply (x : V F) (i : ArchIndex F) :
    archFrequencyMap F x i = adelicArchTrace F (mixedEmbedding.latticeBasis F i * x) := rfl

private theorem archFrequencyMap_injective : Injective (archFrequencyMap F) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hzero (i : ArchIndex F) :
      relativeAdelicTraceRat F (archAdele F x * algebraMap F (A F) (integralBasis F i)) = 0 := by
    rw [archAdele_mul_adele]
    apply Prod.ext
    · apply rationalArchCoordinate_injective
      have h := congrArg (fun a : Euclidean F => a i) (LinearMap.mem_ker.mp hx)
      change archFrequencyMap F x i = 0 at h
      rw [archFrequencyMap_apply, mul_comm] at h
      have he : mixedArch (algebraMap F (A F) (integralBasis F i)) =
          mixedEmbedding.latticeBasis F i := by
        rw [mixedEmbedding.latticeBasis_apply]
        exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
      change adelicArchTrace F (x * mixedArch (algebraMap F (A F) (integralBasis F i))) =
        rationalArchCoordinate 0
      rw [he, h, map_zero]
    · exact relativeAdelicTraceRat_arch_snd F _
  have hz := relativeAdelicTraceRat_sum_traceDual F (archAdele F x)
  simp only [hzero, map_zero, zero_mul, Finset.sum_const_zero] at hz
  have hx := congrArg (mixedArch (F := F)) hz
  have he : mixedArch (archAdele F x) = x :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x
  rw [he, map_zero] at hx
  exact hx.symm

private def archFrequencyChart : V F ≃L[ℝ] Euclidean F :=
  (LinearEquiv.ofBijective (archFrequencyMap F)
    ⟨archFrequencyMap_injective F,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (archLebesgueChart F).toLinearEquiv.finrank_eq.symm).mp (archFrequencyMap_injective F)⟩
    ).toContinuousLinearEquiv

private theorem archTrace_inner (x : Euclidean F) (y : V F) :
    ⟪x, archFrequencyChart F y⟫_ℝ = adelicArchTrace F (archLebesgueChart F x * y) := by
  have hx : archLebesgueChart F x = ∑ i, x i • mixedEmbedding.latticeBasis F i := by
    exact Module.Basis.equivFun_symm_apply _ _
  rw [hx, Finset.sum_mul, map_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪x i, archFrequencyMap F y i⟫_ℝ =
    adelicArchTrace F ((x i • mixedEmbedding.latticeBasis F i) * y)
  rw [RCLike.inner_apply', archFrequencyMap_apply, smul_mul_assoc, map_smul]
  rfl

/-- With the adelic trace pairing, the archimedean Fourier integral of a
Schwartz test is itself a Schwartz function in the mixed archimedean model. -/
theorem exists_archAdelicFourier_homeomorph :
    ∃ T : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ), IsHomeomorph T ∧ ∀ (φ : 𝓢(V F, ℂ)) (ξ : A F),
      (∫ x : V F, φ x * ((standardAdelicCharacter F (archAdele F x * ξ)).toMul : ℂ)) =
        (T φ) (mixedArch ξ) := by
  let e := archLebesgueChart F
  let d := archFrequencyChart F
  let ν : Measure (V F) := (volume : Measure (Euclidean F)).map e
  letI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  let c := (volume : Measure (V F)).addHaarScalarFactor ν
  have hc : (volume : Measure (V F)) = c • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  let A := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) e
  let B := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) d
  let I : 𝓢(Euclidean F, ℂ) →L[ℂ] 𝓢(Euclidean F, ℂ) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv)
      ∘L (SchwartzMap.fourierTransformCLM ℂ)
  let T : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ) := (c : ℂ) • (B ∘L I ∘L A)
  refine ⟨T, ?_, fun φ ξ => ?_⟩
  · let A' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) e.symm
    let B' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) d.symm
    let J : 𝓢(Euclidean F, ℂ) →L[ℂ] 𝓢(Euclidean F, ℂ) := SchwartzMap.fourierTransformCLM ℂ
    let T' : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ) := (c : ℂ)⁻¹ • (A' ∘L J ∘L B')
    have hc₀ : (c : ℂ) ≠ 0 := by
      exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume ν).ne'
    have hA (f : 𝓢(V F, ℂ)) : A' (A f) = f := by
      ext x
      change f (e (e.symm x)) = f x
      rw [e.apply_symm_apply]
    have hA' (f : 𝓢(Euclidean F, ℂ)) : A (A' f) = f := by
      ext x
      change f (e.symm (e x)) = f x
      rw [e.symm_apply_apply]
    have hB (f : 𝓢(Euclidean F, ℂ)) : B' (B f) = f := by
      ext x
      change f (d (d.symm x)) = f x
      rw [d.apply_symm_apply]
    have hB' (f : 𝓢(V F, ℂ)) : B (B' f) = f := by
      ext x
      change f (d.symm (d x)) = f x
      rw [d.symm_apply_apply]
    have hl (f : 𝓢(V F, ℂ)) : T' (T f) = f := by
      change (c : ℂ)⁻¹ • A' (J (B' ((c : ℂ) • B (I (A f))))) = f
      rw [map_smul, map_smul, map_smul, smul_smul, inv_mul_cancel₀ hc₀, one_smul, hB]
      change A' (𝓕 (𝓕⁻ (A f))) = f
      rw [FourierTransform.fourier_fourierInv_eq, hA]
    have hr (f : 𝓢(V F, ℂ)) : T (T' f) = f := by
      change (c : ℂ) • B (I (A ((c : ℂ)⁻¹ • A' (J (B' f))))) = f
      rw [map_smul, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, hA']
      change B (𝓕⁻ (𝓕 (B' f))) = f
      rw [FourierTransform.fourierInv_fourier_eq, hB']
    let U : 𝓢(V F, ℂ) ≃ₜ 𝓢(V F, ℂ) :=
      ⟨⟨T, T', hl, hr⟩, T.continuous, T'.continuous⟩
    exact U.isHomeomorph
  let φ' := A φ
  have hT : (T φ) (mixedArch ξ) =
      (c : ℝ) • (𝓕⁻ φ' : 𝓢(Euclidean F, ℂ)) (d (mixedArch ξ)) := by
    change (c : ℂ) * (𝓕⁻ φ' : 𝓢(Euclidean F, ℂ)) (d (mixedArch ξ)) = _
    rw [Complex.real_smul]
  rw [hc, integral_smul_nnreal_measure, hT]
  change (c : ℝ) • (∫ x : V F, φ x *
    ((standardAdelicCharacter F (archAdele F x * ξ)).toMul : ℂ) ∂ν) =
      (c : ℝ) • (𝓕⁻ φ' : 𝓢(Euclidean F, ℂ)) (d (mixedArch ξ))
  congr 1
  let E : Euclidean F ≃ᵐ V F := e.toHomeomorph.toMeasurableEquiv
  change (∫ x, φ x * ((standardAdelicCharacter F (archAdele F x * ξ)).toMul : ℂ)
    ∂(volume : Measure (Euclidean F)).map E) = _
  rw [integral_map_equiv, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  change φ (e x) * ((standardAdelicCharacter F (archAdele F (e x) * ξ)).toMul : ℂ) =
    Real.fourierChar ⟪x, d (mixedArch ξ)⟫_ℝ • φ (e x)
  have h := archTrace_inner F x (mixedArch ξ)
  change ⟪x, d (mixedArch ξ)⟫_ℝ = adelicArchTrace F (e x * mixedArch ξ) at h
  rw [archAdele_mul_adele, standardAdelicCharacter_arch, h, Real.fourierChar_apply', Circle.smul_def]
  exact mul_comm _ _

theorem exists_archAdelicFourier :
    ∃ T : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ), ∀ (φ : 𝓢(V F, ℂ)) (ξ : A F),
      (∫ x : V F, φ x * ((standardAdelicCharacter F (archAdele F x * ξ)).toMul : ℂ)) =
        (T φ) (mixedArch ξ) := by
  obtain ⟨T, _, hT⟩ := exists_archAdelicFourier_homeomorph F
  exact ⟨T,hT⟩

private theorem finiteAdelicTranslation_mul (u : K F) (ξ : A F) :
    finiteAdelicTranslation F u * ξ = finiteAdelicTranslation F (u * ξ.2) := by
  apply Prod.ext
  · exact zero_mul _
  · rfl

local notation "FourierIntegral" => adelicFourierIntegral F (adelicHaarUnitDomain F)
  (standardAdelicCharacter F)

private theorem exists_bruhatTensor_fourier_factor (ψ : FiniteBruhat F) :
    ∃ (c : ℝ≥0) (ψhat : FiniteBruhat F) (T : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ)),
      IsHomeomorph T ∧ ∀ φ, FourierIntegral (bruhatTensor F φ ψ) =
        (c : ℂ) • bruhatTensor F (T φ) ψhat := by
  let ν := Measure.addHaar (G := K F)
  obtain ⟨c, hc⟩ := adelicFourier_bruhatTensor_factor F ν
  obtain ⟨T, hhomeo, hT⟩ := exists_archAdelicFourier_homeomorph F
  let ψhat : FiniteBruhat F :=
    ⟨⟨finiteAdelicFourier F ν ψ.toLocallyConstant, finiteAdelicFourier_isLocallyConstant F ν ψ⟩,
      finiteAdelicFourier_hasCompactSupport F ν ψ⟩
  refine ⟨c, ψhat, T, hhomeo, fun φ => ?_⟩
  funext ξ
  rw [hc, hT]
  simp_rw [finiteAdelicTranslation_mul]
  change (c : ℝ) • ((T φ) (mixedArch ξ) * ψhat.toLocallyConstant ξ.2) =
    (c : ℂ) • ((T φ) (mixedArch ξ) * ψhat.toLocallyConstant ξ.2)
  rw [Complex.real_smul, smul_eq_mul]

private theorem exists_bruhatTensor_fourier (ψ : FiniteBruhat F) :
    ∃ (ψhat : FiniteBruhat F) (T : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ)),
      ∀ φ, FourierIntegral (bruhatTensor F φ ψ) = bruhatTensor F (T φ) ψhat := by
  obtain ⟨c, ψhat, T, _, hT⟩ := exists_bruhatTensor_fourier_factor F ψ
  refine ⟨ψhat, (c : ℂ) • T, fun φ ↦ (hT φ).trans ?_⟩
  funext ξ
  change (c : ℂ) * ((T φ) (mixedArch ξ) * ψhat.toLocallyConstant ξ.2) =
    ((c : ℂ) * (T φ) (mixedArch ξ)) * ψhat.toLocallyConstant ξ.2
  exact (mul_assoc _ _ _).symm

private theorem bruhat_fourier_integrand_integrable {f : A F → ℂ}
    (hf : f ∈ bruhatSubmodule F) (ξ : A F) :
    Integrable (fun x : A F => f x * ((standardAdelicCharacter F (x * ξ)).toMul : ℂ))
      (adelicHaarUnitDomain F) := by
  let μ := adelicHaarUnitDomain F
  have hInt : Integrable f μ := by
    have he := bruhat_dilate_integrable F hf (1 : Idele F)
    change Integrable (fun x : A F => f (1 * x)) μ at he
    simpa only [one_mul] using he
  have hc : Continuous (fun x : A F => ((standardAdelicCharacter F (x * ξ)).toMul : ℂ)) :=
    continuous_subtype_val.comp (continuous_toMul.comp
      ((standardAdelicCharacter_continuous F).comp (continuous_id.mul continuous_const)))
  apply hInt.mono ((bruhat_continuous F hf).mul hc).aestronglyMeasurable
  exact .of_forall fun x => by simp [Circle.norm_coe]

private theorem adelicFourier_add_bruhat {f h : A F → ℂ}
    (hf : f ∈ bruhatSubmodule F) (hh : h ∈ bruhatSubmodule F) :
    FourierIntegral (f + h) = FourierIntegral f + FourierIntegral h := by
  ext ξ
  simp only [adelicFourierIntegral, Pi.add_apply, add_mul,
    integral_add (bruhat_fourier_integrand_integrable F hf ξ)
      (bruhat_fourier_integrand_integrable F hh ξ)]

private theorem adelicFourier_smul (c : ℂ) (f : A F → ℂ) :
    FourierIntegral (c • f) = c • FourierIntegral f := by
  ext ξ
  simp only [adelicFourierIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

/-- Closure of global Schwartz–Bruhat tests under the normalized additive
Fourier transform. -/
theorem adelicFourier_mem_bruhat {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    FourierIntegral f ∈ bruhatSubmodule F := by
  apply Submodule.span_induction (p := fun f _ =>
    FourierIntegral f ∈ bruhatSubmodule F) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    obtain ⟨ψhat, T, hT⟩ := exists_bruhatTensor_fourier F ψ
    rw [hT]
    exact bruhatTensor_mem F (T φ) ψhat
  · have he : FourierIntegral 0 = 0 := by
      ext ξ
      simp [adelicFourierIntegral]
    rw [he]
    exact (bruhatSubmodule F).zero_mem
  · intro u v hu hv huT hvT
    rw [adelicFourier_add_bruhat F hu hv]
    exact (bruhatSubmodule F).add_mem huT hvT
  · intro c u _ huT
    rw [adelicFourier_smul]
    exact (bruhatSubmodule F).smul_mem _ huT

private def bruhatFourierLinear : GlobalBruhat F →ₗ[ℂ] GlobalBruhat F where
  toFun f :=
    let u := GlobalBruhat.algebraicEquiv F f
    (GlobalBruhat.algebraicEquiv F).symm ⟨FourierIntegral u.val, adelicFourier_mem_bruhat F u.property⟩
  map_add' f g := by
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    change FourierIntegral ((GlobalBruhat.algebraicEquiv F f).val +
      (GlobalBruhat.algebraicEquiv F g).val) = _
    exact adelicFourier_add_bruhat F (GlobalBruhat.algebraicEquiv F f).property
      (GlobalBruhat.algebraicEquiv F g).property
  map_smul' c f := by
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    exact adelicFourier_smul F c (GlobalBruhat.algebraicEquiv F f).val

/-- The normalized Fourier transform is continuous for the final topology
generated by the archimedean Schwartz slices. -/
def GlobalBruhat.fourier : GlobalBruhat F →L[ℂ] GlobalBruhat F where
  toLinearMap := bruhatFourierLinear F
  cont := by
    apply GlobalBruhat.continuous_of_pure F (PolynormableSpace.withSeminorms ℂ (GlobalBruhat F))
    intro ψ
    obtain ⟨ψhat, T, hT⟩ := exists_bruhatTensor_fourier F ψ
    have he (φ : 𝓢(V F, ℂ)) :
        bruhatFourierLinear F (GlobalBruhat.pure F ψ φ) = GlobalBruhat.pure F ψhat (T φ) := by
      apply (GlobalBruhat.algebraicEquiv F).injective
      apply Subtype.ext
      exact hT φ
    simp_rw [he]
    exact (GlobalBruhat.pure_continuous F ψhat).comp T.continuous

@[simp] theorem GlobalBruhat.fourier_apply (f : GlobalBruhat F) :
    (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val =
      FourierIntegral (GlobalBruhat.algebraicEquiv F f).val := rfl

/-- The Fourier factorization on a pure test uses an invertible
archimedean transform and one fixed finite Fourier factor. -/
theorem exists_globalBruhatFourier_pure_factor (ψ : FiniteBruhat F) :
    ∃ (c : ℝ≥0) (ψhat : FiniteBruhat F) (T : 𝓢(V F, ℂ) →L[ℂ] 𝓢(V F, ℂ)),
      IsHomeomorph T ∧ ∀ φ,
        GlobalBruhat.fourier F (GlobalBruhat.pure F ψ φ) =
          (c : ℂ) • GlobalBruhat.pure F ψhat (T φ) := by
  obtain ⟨c, ψhat, T, hT, he⟩ := exists_bruhatTensor_fourier_factor F ψ
  refine ⟨c, ψhat, T, hT, fun φ ↦ ?_⟩
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  exact he φ

/-- Vanishing of the archimedean integral kills the Fourier evaluation
at zero of a pure adelic tensor. -/
theorem globalBruhatFourier_pure_zero_of_archIntegral_zero
    (ψ : FiniteBruhat F) (φ : 𝓢(V F, ℂ)) (hφ : (∫ x : V F, φ x) = 0) :
    GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F (GlobalBruhat.pure F ψ φ)) = 0 := by
  let ν := Measure.addHaar (G := K F)
  obtain ⟨c, hc⟩ := adelicFourier_bruhatTensor_factor F ν
  change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F (GlobalBruhat.pure F ψ φ))).val 0 = 0
  rw [GlobalBruhat.fourier_apply]
  change FourierIntegral (bruhatTensor F φ ψ) 0 = 0
  rw [hc]
  simp only [mul_zero, map_zero, toMul_zero, Circle.coe_one, mul_one, hφ, zero_mul, smul_zero]

/-- The adelic Riemann–Roch theorem (2.2.3.2) as an identity of continuous
functions on the idele class group. -/
theorem adelicTheta_riemannRoch {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    let fhat := adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F) f
    Continuous (adelicTheta F f) ∧
      adelicTheta F f = fun g =>
        (ideleClassNorm F g)⁻¹ • adelicTheta F fhat g⁻¹ +
          (ideleClassNorm F g)⁻¹ • fhat 0 - f 0 := by
  refine ⟨adelicTheta_continuous F (bruhat_theta_continuous_and_invariant hf).1, ?_⟩
  funext g
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F g
  simp only [← map_inv (ideleClassMap F), adelicTheta_mk, ideleClassNorm_mk]
  exact adelicTheta_riemannRoch_of_fourier_mem F hf (adelicFourier_mem_bruhat F hf) g

end

end Masullo
