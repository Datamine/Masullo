import SLocalPaleyWiener
import SchwartzCompactApproximation
import SLocalThetaDualGeneration
import SLocalUnramifiedThetaRange

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev A := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev B := locallyConstantTests (∀ v : S, v.val.adicCompletion F)

/-- The union of the coordinate boxes, expressed as a submodule of tests. -/
def sLocalCompactFourierTests : Submodule ℂ (E F S) :=
  sLocalPaleyWienerTests F S univ

theorem mem_sLocalCompactFourierTests_iff (f : E F S) :
    f ∈ sLocalCompactFourierTests F S ↔
      ∃ X > 0, f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X) := by
  rw [exists_sLocalPaleyWienerBox_iff, sLocalCompactFourierTests, mem_sLocalPaleyWienerTests_iff]
  simp

private theorem compactSupport_arch_finite_product
    (φ : A F) (ψ : B F S) (hφ : HasCompactSupport φ) (c : ℂ) :
    HasCompactSupport (fun a : SAdeles F S ↦
      c * (φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * ψ.val a.2)) := by
  let e := infiniteAdeleMixedHomeomorph F
  have harch : HasCompactSupport ((φ : mixedEmbedding.mixedSpace F → ℂ) ∘ e) :=
    hφ.comp_homeomorph e
  have hfinite : HasCompactSupport ψ.val := ψ.property.2
  apply (harch.prod hfinite).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
  intro a ha
  refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
  · intro hz
    apply ha
    change φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) = 0 at hz
    change c * (φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * ψ.val a.2) = 0
    rw [hz, zero_mul, mul_zero]
  · intro hz
    apply ha
    change ψ.val a.2 = 0 at hz
    change c * (φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * ψ.val a.2) = 0
    rw [hz, mul_zero, mul_zero]

private theorem exists_compactFourier_sequence_pure (φ : A F) (ψ : B F S) :
    ∃ f : ℕ → E F S, (∀ n, f n ∈ sLocalCompactFourierTests F S) ∧
      Tendsto f atTop (𝓝 (sLocalBruhatPure F S φ ψ)) := by
  obtain ⟨c, ψhat, T, hT, he⟩ := exists_globalBruhatFourier_pure_factor F (insertFinite F S ψ)
  let e := hT.homeomorph
  obtain ⟨g, hg, hlim⟩ := exists_schwartz_compactSupport_sequence (T φ)
  let f (n : ℕ) := sLocalBruhatPure F S (e.symm (g n)) ψ
  refine ⟨f, fun n ↦ ?_, ?_⟩
  · change f n ∈ sLocalPaleyWienerTests F S univ
    apply (mem_sLocalPaleyWienerTests_iff F S univ (f n)).mpr
    refine ⟨?_, subset_univ _⟩
    have heval : sLocalBruhatRestriction F S (sLocalFourierCompression F S (f n)).val =
        fun a : SAdeles F S ↦ (c : ℂ) *
          ((g n) (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * (restrictFiniteBruhat F S ψhat).val a.2) := by
      funext a
      change sLocalBruhatRestriction F S
        (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F (GlobalBruhat.pure F
          (insertFinite F S ψ) (e.symm (g n))))).val a = _
      rw [sLocalBruhatCorestrict_restrict, he, map_smul, Pi.smul_apply, sLocalBruhatRestriction_pure]
      have h : T (e.symm (g n)) = g n := e.apply_symm_apply _
      rw [h, smul_eq_mul]
    rw [heval]
    exact compactSupport_arch_finite_product F S (g n) (restrictFiniteBruhat F S ψhat)
      (hg n) (c : ℂ)
  · have h' := (e.symm.continuous.tendsto (T φ)).comp hlim
    have he' : e.symm (T φ) = φ := e.symm_apply_apply _
    rw [he'] at h'
    have hp : Continuous (fun g : A F ↦ sLocalBruhatPure F S g ψ) :=
      (GlobalBruhat.pure_continuous F (insertFinite F S ψ)).subtype_mk _
    exact (hp.tendsto φ).comp h'

/-- Compact Fourier tests are sequentially dense in the actual S-local
Schwartz–Bruhat space. The finite factor already has compact support and the
archimedean factor is approximated using the invertible Fourier transform. -/
theorem exists_sLocalCompactFourier_sequence (f : E F S) :
    ∃ g : ℕ → E F S, (∀ n, g n ∈ sLocalCompactFourierTests F S) ∧
      Tendsto g atTop (𝓝 f) := by
  letI : TopologicalSpace (B F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (A F ⊗[ℂ] B F S) := inductiveTensorTopology _ _
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨x, rfl⟩ := e.surjective f
  induction x using TensorProduct.induction_on with
  | zero =>
    exact ⟨fun _ ↦ 0, fun _ ↦ Submodule.zero_mem _, by simpa only [map_zero] using tendsto_const_nhds⟩
  | tmul φ ψ => exact exists_compactFourier_sequence_pure F S φ ψ
  | add x y hx hy =>
    obtain ⟨f, hf, hf'⟩ := hx
    obtain ⟨g, hg, hg'⟩ := hy
    refine ⟨fun n ↦ f n + g n, fun n ↦ Submodule.add_mem _ (hf n) (hg n), ?_⟩
    simpa only [map_add] using hf'.add hg'

/-- The compact Fourier approximants can be chosen with exactly the same two
evaluation moments as the test they approximate. -/
theorem exists_sLocalCompactFourier_sequence_preserves_moments (f : E F S) :
    ∃ g : ℕ → E F S, (∀ n, g n ∈ sLocalCompactFourierTests F S ∧
      GlobalBruhat.polarEvaluation F (g n).val = GlobalBruhat.polarEvaluation F f.val) ∧
      Tendsto g atTop (𝓝 f) := by
  let D := sLocalCompactFourierTests F S
  let M : E F S →L[ℂ] ℂ × ℂ :=
    (GlobalBruhat.polarEvaluation F).comp (sLocalBruhatImage F S).subtypeL
  let R := M.range
  have hr (x : E F S) : M x ∈ D.map M.toLinearMap := by
    obtain ⟨g, hg, hlim⟩ := exists_sLocalCompactFourier_sequence F S x
    have hclosed := Submodule.closed_of_finiteDimensional (D.map M.toLinearMap)
    exact hclosed.mem_of_tendsto ((M.continuous.tendsto x).comp hlim)
      (Eventually.of_forall fun n ↦ Submodule.mem_map.mpr ⟨g n, hg n, rfl⟩)
  let Md := M.codRestrict R (fun x ↦ ⟨x,rfl⟩)
  let Q : D →L[ℂ] R := Md.comp D.subtypeL
  have hQ : Surjective Q := by
    intro z
    obtain ⟨x,hx⟩ := z.property
    obtain ⟨y,hy,hxy⟩ := Submodule.mem_map.mp (hr x)
    exact ⟨⟨y,hy⟩, Subtype.ext (hxy.trans hx)⟩
  have hQrange : Q.range = ⊤ :=
    LinearMap.range_eq_top_of_surjective Q.toLinearMap hQ
  obtain ⟨J,hJ⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective
    (𝕜 := ℂ) (E := ↥D) (F := ↥R) Q hQrange
  have hEval (z : R) : M (J z).val = z.val :=
    congrArg Subtype.val (DFunLike.congr_fun hJ z)
  obtain ⟨g,hg,hg'⟩ := exists_sLocalCompactFourier_sequence F S f
  let W := D.subtypeL.comp (J.comp Md)
  let v (n : ℕ) := g n - W (g n - f)
  refine ⟨v, fun n ↦ ⟨Submodule.sub_mem _ (hg n) (J (Md (g n - f))).property, ?_⟩, ?_⟩
  · change M (g n - (J (Md (g n - f))).val) = M f
    rw [map_sub, hEval]
    change M (g n) - M (g n - f) = M f
    rw [map_sub, sub_sub_cancel]
  · have hc : Tendsto (fun _ : ℕ ↦ f) atTop (𝓝 f) := tendsto_const_nhds
    have hd : Tendsto (fun n ↦ g n - f) atTop (𝓝 0) := by
      simpa only [sub_self] using hg'.sub hc
    have h := (W.continuous.tendsto 0).comp hd
    rw [map_zero] at h
    simpa only [Function.comp_apply, sub_zero, v] using hg'.sub h

variable {T : Finset (HeightOneSpectrum (𝓞 F))}

/-- Sequential approximation at the enlarged stage of every inserted test.
The approximants lie in positive absolute levels and match both moments. -/
theorem exists_sLocalAbsolutePaleyWienerStage_sequence
    (hST : S ⊆ T) (f : E F S) :
    ∃ g : ℕ → E F T,
      (∀ n, (∃ X > 0, g n ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X)) ∧
        GlobalBruhat.polarEvaluation F (g n).val = GlobalBruhat.polarEvaluation F f.val) ∧
      Tendsto g atTop (𝓝 (sLocalBruhatTransition F hST f)) := by
  obtain ⟨g, hg, hlim⟩ := exists_sLocalCompactFourier_sequence_preserves_moments F S f
  refine ⟨sLocalBruhatTransition F hST ∘ g, fun n ↦ ⟨?_, (hg n).2⟩,
    (sLocalBruhatTransition F hST).continuous.continuousAt.tendsto.comp hlim⟩
  obtain ⟨X, hX, hx⟩ := (mem_sLocalCompactFourierTests_iff F S (g n)).mp (hg n).1
  exact ⟨X,hX, Submodule.mem_map.mpr ⟨g n,hx,rfl⟩⟩

/-- The invariant levels approximate the same inserted tests, with the same
exact preservation of moments. -/
theorem exists_sLocalInvariantPaleyWienerStage_sequence
    (hST : S ⊆ T) (f : E F S) :
    ∃ g : ℕ → E F T,
      (∀ n, (∃ Y > 0, g n ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y)) ∧
        GlobalBruhat.polarEvaluation F (g n).val = GlobalBruhat.polarEvaluation F f.val) ∧
      Tendsto g atTop (𝓝 (sLocalBruhatTransition F hST f)) := by
  obtain ⟨g,hg,hlim⟩ := exists_sLocalAbsolutePaleyWienerStage_sequence F S hST f
  refine ⟨g, fun n ↦ ⟨?_, (hg n).2⟩, hlim⟩
  obtain ⟨X,hX,hx⟩ := (hg n).1
  exact ⟨_, pow_pos hX _, sLocalAbsolutePaleyWienerStageTests_le_invariant F S hST hX.le hx⟩

section Homogeneous

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable (ν : Measure (SLocalThetaNormOne F T)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (SLocalThetaNormOne F T))

/-- Density of the positive levels in the image of the base-stage tests in
the enlarged homogeneous quotient. Both forms hold with the moments fixed,
including when both moments vanish. -/
theorem sLocalPaleyWiener_sequentialDensity_in_transitionImage
    (hST : S ⊆ T) (f : E F S) :
    let M := sLocalHomogeneousThetaKernel F T ν ω
    ∀ region ∈ ({sLocalPaleyWienerBox F S, sLocalPaleyWienerRegion F S} :
        Set (ℝ → Set (SAdeles F S))),
      ∃ g : ℕ → E F T,
        (∀ n, (∃ X > 0, g n ∈ sLocalPaleyWienerStageTests F S hST (region X)) ∧
          GlobalBruhat.polarEvaluation F (g n).val = GlobalBruhat.polarEvaluation F f.val) ∧
        Tendsto (fun n ↦ M.mkQ (g n)) atTop (𝓝 (M.mkQ (sLocalBruhatTransition F hST f))) := by
  dsimp only
  intro region hr
  rcases hr with he | he
  · subst region
    obtain ⟨g,hg,hlim⟩ := exists_sLocalAbsolutePaleyWienerStage_sequence F S hST f
    exact ⟨g,hg, (sLocalHomogeneousThetaKernel F T ν ω).mkQL.continuous.continuousAt.tendsto.comp hlim⟩
  · have he' : region = sLocalPaleyWienerRegion F S := he
    subst region
    obtain ⟨g,hg,hlim⟩ := exists_sLocalInvariantPaleyWienerStage_sequence F S hST f
    exact ⟨g,hg, (sLocalHomogeneousThetaKernel F T ν ω).mkQL.continuous.continuousAt.tendsto.comp hlim⟩

end Homogeneous


local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

/-- Both positive Paley–Wiener families exhaust the enlarged homogeneous
space sequentially, also on the image of the common moment kernel.
The enlargement uses the integer-ring insertion of the stage transition. -/
theorem sLocalPaleyWiener_sequentialDensity_of_unramified
    (hST : S ⊆ T) (hs : Surjective (sIdeleClassInclusion F S))
    (ωG : PontryaginDual (normOneIdeleClass F))
    (hu : globalNormOneCharacter F ωG ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
    (νT : Measure (SLocalThetaNormOne F T)) [νT.IsHaarMeasure]
    (f : E F T) :
    let hsT := sIdeleClassInclusion_surjective_mono F hST hs
    let huT := sUnramified_mono F hST hu
    let ωT := sLocalNormOneCharacterOfGlobal F ωG T hsT huT
    let M := sLocalHomogeneousThetaKernel F T νT ωT
    ∀ region ∈ ({sLocalPaleyWienerBox F S, sLocalPaleyWienerRegion F S} :
        Set (ℝ → Set (SAdeles F S))),
      ∃ g : ℕ → E F T,
        (∀ n, (∃ X > 0, g n ∈ sLocalPaleyWienerStageTests F S hST (region X)) ∧
          (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F (g n).val = 0)) ∧
        Tendsto (fun n ↦ M.mkQ (g n)) atTop (𝓝 (M.mkQ f)) := by
  dsimp only
  intro region hregion
  obtain ⟨a,ha,hm⟩ :=
    exists_sLocalBaseRepresentative_preserves_zero_moments F νG ωG η hν hST hs hu νT f
  let hsT := sIdeleClassInclusion_surjective_mono F hST hs
  let huT := sUnramified_mono F hST hu
  let ωT := sLocalNormOneCharacterOfGlobal F ωG T hsT huT
  obtain ⟨g,hg,hlim⟩ :=
    sLocalPaleyWiener_sequentialDensity_in_transitionImage F S νT ωT hST a region hregion
  rw [← ha] at hlim
  exact ⟨g,fun n ↦ ⟨(hg n).1, fun h ↦ (hg n).2.trans (hm h)⟩,hlim⟩

end

end Masullo
