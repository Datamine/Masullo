import ModulatedSobolevProfiles
import ModulatedSobolevTests

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

local notation "Profiles" => (modulatedExponentialProfiles (K := K))

/-- The actual function of the angular and radial variables. -/
def modulatedProfileFunction : Profiles →ₗ[ℂ] (K × ℝ → ℂ) where
  toFun f p := f.val p.2 p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Strict support of the logarithmic profile, in the sense of the manuscript. -/
def modulatedExponentialProfileCutoff (U : Set ℝ) : Submodule ℂ Profiles where
  carrier := {f | tsupport (modulatedProfileFunction f) ⊆ Prod.snd ⁻¹' U}
  zero_mem' := by simp [modulatedProfileFunction]
  add_mem' {f g} hf hg := by
    change tsupport (modulatedProfileFunction (f + g)) ⊆ _
    rw [map_add]
    exact (tsupport_add _ _).trans (union_subset hf hg)
  smul_mem' c f hf := by
    change tsupport (modulatedProfileFunction (c • f)) ⊆ _
    rw [map_smul]
    exact (tsupport_smul_subset_right (fun _ => c) _).trans hf

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- Linear inclusion of the actual function tests into the weighted Hilbert space. -/
def modulatedExponentialProfile_inclusion (b : ℝ) (N : ℕ) :
    Profiles →ₗ[ℂ] Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) where
  toFun := modulatedExponentialProfile_toLp μ b N
  map_add' f g := by
    apply Lp.ext
    filter_upwards [modulatedExponentialProfile_toLp_ae μ b N (f + g),
      modulatedExponentialProfile_toLp_ae μ b N f, modulatedExponentialProfile_toLp_ae μ b N g,
      Lp.coeFn_add (modulatedExponentialProfile_toLp μ b N f)
        (modulatedExponentialProfile_toLp μ b N g)] with p h hf hg hsum
    exact h.trans (hsum.trans (congrArg₂ (· + ·) hf hg)).symm
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [modulatedExponentialProfile_toLp_ae μ b N (c • f),
      modulatedExponentialProfile_toLp_ae μ b N f,
      Lp.coeFn_smul c (modulatedExponentialProfile_toLp μ b N f)] with p h hf hm
    exact h.trans (hm.trans (congrArg (c • ·) hf)).symm

/-- Supported function tests map into the weighted indicator range. -/
def modulatedExponentialProfile_cutoffInclusion (b : ℝ) (N : ℕ) (U : Set ℝ) :
    modulatedExponentialProfileCutoff (K := K) U →ₗ[ℂ]
      lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) U :=
  ((modulatedExponentialProfile_inclusion μ b N).comp
    (modulatedExponentialProfileCutoff (K := K) U).subtype).codRestrict _ fun f => by
      change ∀ᵐ p ∂μ.prod (stripMeasure b b (2 * (N : ℝ))), p.2 ∉ U →
        modulatedExponentialProfile_toLp μ b N f.val p = 0
      filter_upwards [modulatedExponentialProfile_toLp_ae μ b N f.val] with p hp hU
      exact hp.trans (image_eq_zero_of_notMem_tsupport
        (fun h => hU (f.property h)) :
        modulatedProfileFunction f.val p = 0)

variable [CommGroup K] [IsTopologicalGroup K]

private def separatedExponentialProfile (χ : PontryaginDual K)
    (φ : PositiveRealExponentialDecay univ) : Profiles := by
  let χ' : C(K, ℂ) := ⟨fun k => (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩
  let A := (ContinuousLinearMap.id ℂ ℂ).smulRight χ'
  refine ⟨fun x => A (φ.val x), fun b => ?_⟩
  let F := logExponentialDecayTwist univ ⟨b, mem_univ _⟩ φ
  refine ⟨F.postcompCLM A, fun x => ?_⟩
  rw [SchwartzMap.postcompCLM_apply,
    show F x = _ from logExponentialDecayTwist_apply univ ⟨b, mem_univ _⟩ φ x]
  change A ((Real.exp (b * x) : ℂ) • φ.val x) = _
  exact map_smul A _ _

omit [T2Space K] [MeasurableSpace K] [BorelSpace K] [IsTopologicalGroup K] in
private theorem separatedExponentialProfile_apply (χ : PontryaginDual K)
    (φ : PositiveRealExponentialDecay univ) (p : K × ℝ) :
    modulatedProfileFunction (separatedExponentialProfile χ φ) p =
      φ.val p.2 * (χ p.1 : ℂ) := rfl

private def separatedExponentialProfileCutoff {U : Set ℝ} (χ : PontryaginDual K)
    (φ : compactRadialTests U) : modulatedExponentialProfileCutoff (K := K) U := by
  refine ⟨separatedExponentialProfile χ φ.val, ?_⟩
  change tsupport (modulatedProfileFunction (separatedExponentialProfile χ φ.val)) ⊆ Prod.snd ⁻¹' U
  have hsub : support (modulatedProfileFunction (separatedExponentialProfile χ φ.val)) ⊆
      (Prod.snd : K × ℝ → ℝ) ⁻¹' tsupport φ.val.val := by
    intro p hp
    by_contra hn
    exact hp (by
      rw [separatedExponentialProfile_apply,
        image_eq_zero_of_notMem_tsupport (show p.2 ∉ tsupport φ.val.val from hn), zero_mul])
  exact (closure_minimal hsub (isClosed_tsupport _ |>.preimage continuous_snd)).trans
    (preimage_mono φ.property.2)

omit [IsTopologicalGroup K] in
/-- The compact separated tests are contained in the full exponential
Schwartz profile class with the same strict support. -/
theorem modulatedSeparatedTest_in_profileCutoffRange (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U) (χ : PontryaginDual K) (φ : compactRadialTests U) :
    modulatedSeparatedTest μ b (2 * (N : ℝ)) hU χ φ ∈
      LinearMap.range (modulatedExponentialProfile_cutoffInclusion μ b N U) := by
  let f := separatedExponentialProfileCutoff χ φ
  refine ⟨f, Subtype.ext ?_⟩
  apply Lp.ext
  filter_upwards [modulatedExponentialProfile_toLp_ae μ b N f.val,
    modulatedSeparatedTest_ae μ b (2 * (N : ℝ)) hU χ φ] with p hp hq
  change modulatedExponentialProfile_toLp μ b N f.val p =
    (modulatedSeparatedTest μ b (2 * (N : ℝ)) hU χ φ).val p
  rw [hp, hq]
  exact mul_comm _ _

/-- The full supported exponential profile tests fill the indicator range
after completion under the manuscript's weighted norm. -/
theorem modulatedExponentialProfile_cutoff_dense [μ.WeaklyRegular] (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U) :
    DenseRange (modulatedExponentialProfile_cutoffInclusion μ b N U) := by
  let A := modulatedExponentialProfile_cutoffInclusion μ b N U
  have hA : Submodule.span ℂ (range (fun p : PontryaginDual K × compactRadialTests U =>
      modulatedSeparatedTest μ b (2 * (N : ℝ)) hU p.1 p.2)) ≤ LinearMap.range A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨χ, φ⟩, rfl⟩
    exact modulatedSeparatedTest_in_profileCutoffRange μ b N hU χ φ
  have h := Submodule.topologicalClosure_mono hA
  rw [modulatedSeparatedTest_dense μ b (2 * (N : ℝ)) hU] at h
  intro u
  exact h (Submodule.mem_top (x := u))

/-- Without a support restriction the exponential profile tests are dense
in the full weighted product Hilbert space. -/
theorem modulatedExponentialProfile_dense [μ.WeaklyRegular] (b : ℝ) (N : ℕ) :
    DenseRange (modulatedExponentialProfile_inclusion μ b N) := by
  let S := lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) (univ : Set ℝ)
  have hsurj : Surjective (fun u : S => u.val) := fun u =>
    ⟨⟨u, by
      change ∀ᵐ p ∂μ.prod (stripMeasure b b (2 * (N : ℝ))), p.2 ∉ (univ : Set ℝ) → u p = 0
      simp⟩, rfl⟩
  exact DenseRange.of_comp (hsurj.denseRange.comp
    (modulatedExponentialProfile_cutoff_dense μ b N isOpen_univ) continuous_subtype_val)

end
end Masullo
