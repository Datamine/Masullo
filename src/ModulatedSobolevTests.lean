import ModulatedSobolevGroup
import CompactCharacterCompleteness

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

theorem dense_span_tmul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] {A : Set E} {B : Set F}
    (hA : (Submodule.span ℂ A).topologicalClosure = ⊤)
    (hB : (Submodule.span ℂ B).topologicalClosure = ⊤) :
    Dense (Submodule.span ℂ ((fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) '' (A ×ˢ B)) : Set (E ⊗[ℂ] F)) := by
  let C := Submodule.span ℂ ((fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) '' (A ×ˢ B))
  have hspan (u : E) (hu : u ∈ Submodule.span ℂ A) (v : F) (hv : v ∈ Submodule.span ℂ B) :
      u ⊗ₜ[ℂ] v ∈ C := by
    induction hu using Submodule.span_induction with
    | zero => simp
    | add u w _ _ hu hw => rw [TensorProduct.add_tmul]; exact C.add_mem hu hw
    | smul a u _ hu => rw [← TensorProduct.smul_tmul']; exact C.smul_mem a hu
    | mem u hu =>
      induction hv using Submodule.span_induction with
      | mem v hv => exact Submodule.subset_span ⟨(u, v), ⟨hu, hv⟩, rfl⟩
      | zero => simp
      | add v w _ _ hv hw => rw [TensorProduct.tmul_add]; exact C.add_mem hv hw
      | smul a v _ hv => rw [TensorProduct.tmul_smul]; exact C.smul_mem a hv
  have hdA : Dense (Submodule.span ℂ A : Set E) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hA, Submodule.top_coe]
  have hdB : Dense (Submodule.span ℂ B : Set F) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hB, Submodule.top_coe]
  have hpure (u : E) (v : F) : u ⊗ₜ[ℂ] v ∈ C.topologicalClosure := by
    have hp := mem_closure_image (TensorProduct.continuous_tmul (𝕜 := ℂ) (E := E) (F := F)).continuousAt ((hdA.prod hdB) (u, v))
    exact closure_mono (by rintro _ ⟨⟨a, b⟩, hab, rfl⟩; exact hspan a hab.1 b hab.2) hp
  change Dense (C : Set (E ⊗[ℂ] F))
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
  apply Set.eq_univ_of_forall
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact C.topologicalClosure.zero_mem
  | tmul u v => exact hpure u v
  | add x y hx hy => exact C.topologicalClosure.add_mem hx hy

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

private def continuousCharacter (χ : PontryaginDual K) : C(K, ℂ) :=
  ⟨fun k => (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩

variable (μ : Measure K) [IsFiniteMeasure μ]

/-- A compact character viewed as a vector in Haar L². -/
def compactCharacterLp (χ : PontryaginDual K) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ (continuousCharacter χ)

omit [IsTopologicalGroup K] [T2Space K] in
theorem compactCharacterLp_ae (χ : PontryaginDual K) :
    (compactCharacterLp μ χ : K → ℂ) =ᵐ[μ] fun k => (χ k : ℂ) :=
  (continuousCharacter χ).coeFn_toLp (p := 2) (𝕜 := ℂ) μ

theorem dense_span_compactCharacterLp [μ.WeaklyRegular] :
    (Submodule.span ℂ (range (compactCharacterLp μ))).topologicalClosure = ⊤ := by
  let v : PontryaginDual K →* C(K, ℂ) :=
    { toFun := continuousCharacter, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  have hd : DenseRange T := ContinuousMap.toLp_denseRange ℂ μ ℂ (by simp)
  have h := hd.topologicalClosure_map_submodule (dense_span_pontryaginDual v (fun _ _ => rfl))
  rwa [Submodule.map_span, ← range_comp] at h

local notation "RadialTest" => PositiveRealExponentialDecay (univ : Set ℝ)

abbrev compactRadialTests (U : Set ℝ) :=
  {f : RadialTest // HasCompactSupport f.val ∧ tsupport f.val ⊆ U}

private def compactRadialWeighted (a b s : ℝ) (U : Set ℝ) (f : compactRadialTests U) :
    supportedSobolevCompletion a b s U :=
  supportedSobolevTest a b s U f.val
    (fun _ hx => image_eq_zero_of_notMem_tsupport (fun h => hx (f.property.2 h)))

private theorem denseRange_compactRadialWeighted (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    DenseRange (compactRadialWeighted a b s U) := by
  intro u
  rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
  have hu := u.property
  change u.val ∈ (supportedSobolevCompletion a b s U : Set _) at hu
  rw [supportedSobolevCompletion_eq_closure_of_compactTests a b s hU] at hu
  apply (closure_mono ?_) hu
  rintro _ ⟨f, hf, hs, rfl⟩
  exact ⟨compactRadialWeighted a b s U ⟨f, hf, hs⟩, ⟨⟨f, hf, hs⟩, rfl⟩, rfl⟩

/-- A separated compact test in the product weighted cutoff. -/
def modulatedIntervalSeparatedTest (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (f : compactRadialTests U) :
    lpTwoRadialSupport μ (stripMeasure a b s) U :=
  modulatedIntervalTensorEquiv μ a b s hU
    ((compactCharacterLp μ χ ⊗ₜ[ℂ] compactRadialWeighted a b s U f :
      Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s U) :
      Completion (Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s U))

omit [IsTopologicalGroup K] [T2Space K] in
theorem modulatedIntervalSeparatedTest_ae (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (f : compactRadialTests U) :
    ((modulatedIntervalSeparatedTest μ a b s hU χ f).val : K × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure a b s)]
      fun p => (χ p.1 : ℂ) * f.val.val p.2 := by
  unfold modulatedIntervalSeparatedTest
  rw [modulatedIntervalTensorEquiv_tmul]
  have ha := Measure.quasiMeasurePreserving_fst (μ := μ) (ν := stripMeasure a b s)
  have hb := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := stripMeasure a b s)
  have hf := stripSobolevTest_ae univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f.val
  filter_upwards [lpTwoProduct_ae (compactCharacterLp μ χ) (compactRadialWeighted a b s U f).val,
    ha.ae_eq_comp (compactCharacterLp_ae μ χ), hb.ae_eq_comp hf] with p h hχ hf
  change compactCharacterLp μ χ p.1 = (χ p.1 : ℂ) at hχ
  change (compactRadialWeighted a b s U f).val p.2 = f.val.val p.2 at hf
  rw [h, hχ, hf]

/-- Separated compact character tests and compact smooth radial tests have dense span
in the whole supported weighted product space. Taking the open set to be the whole line
gives the full weighted space. -/
theorem modulatedIntervalSeparatedTest_dense [μ.WeaklyRegular] (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    (Submodule.span ℂ (range (fun p : PontryaginDual K × compactRadialTests U =>
      modulatedIntervalSeparatedTest μ a b s hU p.1 p.2))).topologicalClosure = ⊤ := by
  let A := (range (compactCharacterLp μ))
  let B := range (compactRadialWeighted a b s U)
  have hB : (Submodule.span ℂ B).topologicalClosure = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact closure_mono Submodule.subset_span (denseRange_compactRadialWeighted a b s hU x)
  let tm (p : Lp ℂ 2 μ × supportedSobolevCompletion a b s U) := p.1 ⊗ₜ[ℂ] p.2
  let C := Submodule.span ℂ (tm '' (A ×ˢ B))
  have hC : Dense (C : Set (Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s U)) :=
    dense_span_tmul (dense_span_compactCharacterLp μ) hB
  let T := (modulatedIntervalTensorEmbedding μ a b s hU).toContinuousLinearMap
  have hT : DenseRange T := denseRange_modulatedIntervalTensorEmbedding μ a b s hU
  have htest (χ : PontryaginDual K) (f : compactRadialTests U) :
      T (tm (compactCharacterLp μ χ, compactRadialWeighted a b s U f)) =
        modulatedIntervalSeparatedTest μ a b s hU χ f := by
    apply Subtype.ext
    exact (modulatedIntervalTensorEmbedding_tmul μ a b s hU _ _).trans
      (modulatedIntervalTensorEquiv_tmul μ a b s hU _ _).symm
  have he : T '' (tm '' (A ×ˢ B)) = range (fun p : PontryaginDual K × compactRadialTests U =>
      modulatedIntervalSeparatedTest μ a b s hU p.1 p.2) := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨_, _⟩, ⟨⟨χ, rfl⟩, ⟨f, rfl⟩⟩, rfl⟩, rfl⟩
      exact ⟨(χ, f), (htest χ f).symm⟩
    · rintro ⟨⟨χ, f⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨⟨χ, rfl⟩, ⟨f, rfl⟩⟩, rfl⟩, htest χ f⟩
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq]
  apply hT.dense_of_mapsTo T.continuous hC
  intro x hx
  change T x ∈ Submodule.span ℂ _
  rw [← he]
  change T.toLinearMap x ∈ Submodule.span ℂ (T.toLinearMap '' (tm '' (A ×ˢ B)))
  rw [← Submodule.map_span T.toLinearMap]
  exact ⟨x, hx, rfl⟩

abbrev modulatedSeparatedTest (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (f : compactRadialTests U) :
    lpTwoRadialSupport μ (stripMeasure b b s) U :=
  modulatedIntervalSeparatedTest μ b b s hU χ f

omit [IsTopologicalGroup K] [T2Space K] in
theorem modulatedSeparatedTest_ae (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (f : compactRadialTests U) :
    ((modulatedSeparatedTest μ b s hU χ f).val : K × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure b b s)]
      fun p => (χ p.1 : ℂ) * f.val.val p.2 :=
  modulatedIntervalSeparatedTest_ae μ b b s hU χ f

theorem modulatedSeparatedTest_dense [μ.WeaklyRegular] (b s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) :
    (Submodule.span ℂ (range (fun p : PontryaginDual K × compactRadialTests U =>
      modulatedSeparatedTest μ b s hU p.1 p.2))).topologicalClosure = ⊤ :=
  modulatedIntervalSeparatedTest_dense μ b b s hU

section GroupTests

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

/-- Separated tests transported to the weighted group space. -/
def modulatedGroupSeparatedTest (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual m.toMonoidHom.ker) (f : compactRadialTests U) :
    modulatedGroupCutoff m τ hτ ν b s U :=
  (modulatedGroupCutoffEquiv m τ hτ ν b s U).symm (modulatedSeparatedTest ν b s hU χ f)

omit [T2Space G] in
theorem modulatedGroupSeparatedTest_ae (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual m.toMonoidHom.ker) (f : compactRadialTests U) :
    ∀ᵐ p ∂ν.prod (stripMeasure b b s),
      (modulatedGroupSeparatedTest m τ hτ ν b s hU χ f).val
        (τ (Multiplicative.ofAdd p.2) * p.1.val) = (χ p.1 : ℂ) * f.val.val p.2 := by
  let v := modulatedGroupSeparatedTest m τ hτ ν b s hU χ f
  have hp := modulatedSobolevGroupEquiv_ae m τ hτ ν b s v.val
  have he : modulatedGroupCutoffEquiv m τ hτ ν b s U v = modulatedSeparatedTest ν b s hU χ f :=
    (modulatedGroupCutoffEquiv m τ hτ ν b s U).apply_symm_apply _
  change ((modulatedGroupCutoffEquiv m τ hτ ν b s U v).val : m.toMonoidHom.ker × ℝ → ℂ)
    =ᵐ[ν.prod (stripMeasure b b s)] _ at hp
  rw [he] at hp
  exact hp.symm.trans (modulatedSeparatedTest_ae ν b s hU χ f)

/-- A separated test has an actual continuous representative with compact
support strictly inside the chosen logarithmic cutoff. -/
theorem modulatedGroupSeparatedTest_compactProfile (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual m.toMonoidHom.ker) (f : compactRadialTests U) :
    ∃ g : C(G, ℂ), HasCompactSupport g ∧ tsupport g ⊆ modulatedLog m ⁻¹' U ∧
      (∀ (x : ℝ) (k : m.toMonoidHom.ker),
        g (τ (Multiplicative.ofAdd x) * k.val) = (χ k : ℂ) * f.val.val x) ∧
      ∀ᵐ p ∂ν.prod (stripMeasure b b s),
        (modulatedGroupSeparatedTest m τ hτ ν b s hU χ f).val
          (τ (Multiplicative.ofAdd p.2) * p.1.val) =
        g (τ (Multiplicative.ofAdd p.2) * p.1.val) := by
  let K := m.toMonoidHom.ker
  let e := modulatedLogSplit m τ hτ
  let F := f.val.val
  have hF : Continuous F := by
    apply (logExponentialDecayTwist univ ⟨0, mem_univ _⟩ f.val).continuous.congr
    intro x
    simpa only [F, Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
      (logExponentialDecayTwist_apply univ ⟨0, mem_univ _⟩ f.val x)
  let g : C(G, ℂ) :=
    ⟨fun y => (χ (e.symm y).2 : ℂ) * F (e.symm y).1,
      ((continuous_subtype_val.comp χ.continuous).comp (continuous_snd.comp e.symm.continuous)).mul
        (hF.comp (continuous_fst.comp e.symm.continuous))⟩
  have hg (x : ℝ) (k : K) : g (τ (Multiplicative.ofAdd x) * k.val) = (χ k : ℂ) * F x := by
    change (χ (e.symm (e (x, k))).2 : ℂ) * F (e.symm (e (x, k))).1 = _
    rw [e.symm_apply_apply]
  let B := e '' (tsupport F ×ˢ (univ : Set K))
  have hB : IsCompact B := (f.property.1.isCompact.prod isCompact_univ).image e.continuous
  have hsub : tsupport g ⊆ B := by
    apply closure_minimal _ hB.isClosed
    intro y hy
    obtain ⟨⟨x, k⟩, rfl⟩ := e.surjective y
    have hx : x ∈ tsupport F := by
      by_contra! h
      exact hy ((hg x k).trans (by rw [image_eq_zero_of_notMem_tsupport h, mul_zero]))
    exact ⟨(x, k), ⟨hx, mem_univ _⟩, rfl⟩
  have hU' : tsupport g ⊆ modulatedLog m ⁻¹' U := by
    intro y hy
    obtain ⟨⟨x, k⟩, ⟨hx, _⟩, rfl⟩ := hsub hy
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd x) * k.val)) ∈ U
    rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one]
    exact f.property.2 hx
  refine ⟨g, hB.of_isClosed_subset (isClosed_tsupport _) hsub, hU', hg, ?_⟩
  filter_upwards [modulatedGroupSeparatedTest_ae m τ hτ ν b s hU χ f] with p hp
  exact hp.trans (hg p.2 p.1).symm

/-- The separated tests have dense span for the physical group Haar measure. -/
theorem modulatedGroupSeparatedTest_dense [ν.WeaklyRegular] (b s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    (Submodule.span ℂ (range (fun p : PontryaginDual m.toMonoidHom.ker × compactRadialTests U =>
      modulatedGroupSeparatedTest m τ hτ ν b s hU p.1 p.2))).topologicalClosure = ⊤ := by
  let T := (modulatedGroupCutoffEquiv m τ hτ ν b s U).symm.toContinuousLinearEquiv
  have H := T.surjective.denseRange.topologicalClosure_map_submodule
    (f := T.toContinuousLinearMap) (modulatedSeparatedTest_dense ν b s hU)
  rwa [Submodule.map_span, ← range_comp] at H

/-- Bounded evaluations on the completed group tensor are already determined
by their values on the separated compact test functions. -/
theorem modulatedGroupMellin_eq_of_separated [ν.WeaklyRegular] (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U)
    (L₁ L₂ : StrongDual ℂ (Completion
      (Lp ℂ 2 ν ⊗[ℂ] supportedMellinLineCompletion b N U)))
    (h : ∀ χ f,
      L₁ (modulatedGroupMellinEquiv m τ hτ ν b N hU
        (modulatedGroupSeparatedTest m τ hτ ν b (2 * (N : ℝ)) hU χ f)) =
      L₂ (modulatedGroupMellinEquiv m τ hτ ν b N hU
        (modulatedGroupSeparatedTest m τ hτ ν b (2 * (N : ℝ)) hU χ f))) : L₁ = L₂ := by
  let s : ℝ := 2 * (N : ℝ)
  let M := (modulatedGroupMellinEquiv m τ hτ ν b N hU).toContinuousLinearEquiv
  let Q := (L₁ - L₂).comp M.toContinuousLinearMap
  let C := Submodule.span ℂ (range
    (fun p : PontryaginDual m.toMonoidHom.ker × compactRadialTests U =>
      modulatedGroupSeparatedTest m τ hτ ν b s hU p.1 p.2))
  have hC : C ≤ Q.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨χ, f⟩, rfl⟩
    exact sub_eq_zero.mpr (h χ f)
  have hT := Submodule.topologicalClosure_minimal _ hC Q.isClosed_ker
  rw [modulatedGroupSeparatedTest_dense m τ hτ ν b s hU] at hT
  ext v
  obtain ⟨u, rfl⟩ := M.surjective v
  exact sub_eq_zero.mp (hT (Submodule.mem_top (x := u)))

end GroupTests

end

end Masullo
