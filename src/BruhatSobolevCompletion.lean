import BruhatSplitSchwartz
import ModulatedSobolevGroupProfiles
import ModulatedSobolevSequence
import ModulatedSobolevTests

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialInductive m (Set.univ : Set ℝ)
local notation "Profiles" => (@modulatedExponentialProfiles K _ _)

private def bruhatSobolevTwist (b : ℝ) : E →L[ℂ] 𝓢(ℝ, C(K, ℂ)) :=
  (exists_bruhatSplitSchwartz m τ hτ).choose.comp (modulatedDecayTwistCLM m univ ⟨b, mem_univ b⟩)

omit [MeasurableSpace G] [BorelSpace G] in
private theorem bruhatSobolevTwist_apply (b : ℝ) (f : E) (x : ℝ) (k : K) :
    bruhatSobolevTwist m τ hτ b f x k =
      (Real.exp (b * x) : ℂ) * f.val (τ (Multiplicative.ofAdd x) * k.val) := by
  let g := τ (Multiplicative.ofAdd x) * k.val
  have h := (exists_bruhatSplitSchwartz m τ hτ).choose_spec
    (modulatedDecayTwistCLM m univ ⟨b, mem_univ b⟩ f) x k
  change bruhatSobolevTwist m τ hτ b f x k = modulatedExponentialWeight m b f.val g at h
  have hg : (m g).toAdd = x := by
    dsimp only [g]
    rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one]
    rfl
  simpa only [modulatedExponentialWeight_apply, hg, Complex.real_smul] using h

/-- The actual inductive Bruhat decay tests have the uniform radial
Schwartz profile used by their Mellin transform. -/
def bruhatSobolevProfile : E →ₗ[ℂ] Profiles := by
  let L : E →ₗ[ℂ] (ℝ → C(K, ℂ)) :=
    { toFun := fun f x ↦ bruhatSobolevTwist m τ hτ 0 f x
      map_add' f g := funext fun x ↦ congrArg (fun F : 𝓢(ℝ, C(K, ℂ)) ↦ F x)
        (map_add (bruhatSobolevTwist m τ hτ 0) f g)
      map_smul' c f := funext fun x ↦ congrArg (fun F : 𝓢(ℝ, C(K, ℂ)) ↦ F x)
        (map_smul (bruhatSobolevTwist m τ hτ 0) c f) }
  refine L.codRestrict _ fun f b ↦ ⟨bruhatSobolevTwist m τ hτ b f, fun x ↦ ?_⟩
  apply ContinuousMap.ext
  intro k
  change bruhatSobolevTwist m τ hτ b f x k =
    (Real.exp (b * x) : ℂ) * bruhatSobolevTwist m τ hτ 0 f x k
  rw [bruhatSobolevTwist_apply, bruhatSobolevTwist_apply, zero_mul, Real.exp_zero,
    Complex.ofReal_one, one_mul]

omit [MeasurableSpace G] [BorelSpace G] in
theorem bruhatSobolevProfile_apply (f : E) (x : ℝ) (k : K) :
    (bruhatSobolevProfile m τ hτ f).val x k = f.val (τ (Multiplicative.ofAdd x) * k.val) := by
  change bruhatSobolevTwist m τ hτ 0 f x k = _
  rw [bruhatSobolevTwist_apply, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem bruhatSobolevProfile_twist (b : ℝ) (f : E) :
    modulatedProfileTwist b (bruhatSobolevProfile m τ hτ f) = bruhatSobolevTwist m τ hτ b f := by
  apply SchwartzMap.ext
  intro x
  apply ContinuousMap.ext
  intro k
  change ((bruhatSobolevProfile m τ hτ f).property b).choose x k = _
  rw [((bruhatSobolevProfile m τ hτ f).property b).choose_spec x,
    bruhatSobolevTwist_apply]
  change (Real.exp (b * x) : ℂ) * (bruhatSobolevProfile m τ hτ f).val x k = _
  rw [bruhatSobolevProfile_apply]

variable (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

include hτ ν

set_option maxHeartbeats 2200000 in
/-- The continuous weighted inclusion from the manuscript's entire decay
space, in its original inductive topology. -/
def bruhatSobolevInclusion (b : ℝ) (N : ℕ) : E →L[ℂ]
    Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))) := by
  let T := modulatedGroupProfile_inclusion m τ hτ ν b N
  let P := bruhatSobolevProfile m τ hτ
  have hP : Continuous (fun f : E ↦ modulatedProfileTwist b (P f)) :=
    (bruhatSobolevTwist m τ hτ b).continuous.congr (fun f ↦
      (bruhatSobolevProfile_twist m τ hτ b f).symm)
  exact ⟨T.comp P, modulatedGroupProfile_inclusion_continuous m τ hτ ν b N P hP⟩

set_option maxHeartbeats 1600000 in
theorem bruhatSobolevInclusion_ae (b : ℝ) (N : ℕ) (f : E) :
    (bruhatSobolevInclusion m τ hτ ν b N f : G → ℂ)
      =ᵐ[modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))] f.val := by
  refine (modulatedGroupProfile_inclusion_ae m τ hτ ν b N
    (bruhatSobolevProfile m τ hτ f)).trans (.of_forall fun g ↦ ?_)
  obtain ⟨⟨x, k⟩, rfl⟩ := (modulatedLogSplit m τ hτ).surjective g
  exact (modulatedGroupProfile_onSplit m τ hτ _ x k).trans
    (bruhatSobolevProfile_apply m τ hτ f x k)

theorem bruhatSobolevInclusion_injective [ν.IsOpenPosMeasure] (b : ℝ) (N : ℕ) :
    Injective (bruhatSobolevInclusion m τ hτ ν b N) := by
  intro f g hfg
  have he := modulatedGroupProfile_inclusion_injective m τ hτ ν b N hfg
  apply ModulatedExponentialInductive.algebraicEquiv.injective
  apply Subtype.ext
  funext y
  obtain ⟨⟨x, k⟩, rfl⟩ := (modulatedLogSplit m τ hτ).surjective y
  exact (bruhatSobolevProfile_apply m τ hτ f x k).symm.trans
    ((congrArg (fun F : Profiles ↦ F.val x k) he).trans
      (bruhatSobolevProfile_apply m τ hτ g x k))

/-- Characterwise the completed transform is the Mellin line transform of
the integral over the actual norm-one fibers. -/
theorem bruhatSobolevMellin_onTest (b : ℝ) (N : ℕ) (χ : PontryaginDual K) (f : E) :
    ∃ p : PositiveRealExponentialDecay univ,
      (∀ x : ℝ, p.val x = ∫ k : K, f.val (τ (Multiplicative.ofAdd x) * k.val) *
        (χ k : ℂ) ∂ν) ∧
      (modulatedMellinLineCharacter ν b N χ
        (modulatedGroupFullMellin m τ hτ ν b N (bruhatSobolevInclusion m τ hτ ν b N f)) :
          MellinTraceHilbert N) = mellinLineTest b N p := by
  let F := bruhatSobolevProfile m τ hτ f
  refine ⟨modulatedExponentialProfile_character ν χ F, fun x ↦ ?_,
    modulatedGroupFullMellin_character_onProfile m τ hτ ν b N χ F⟩
  rw [modulatedExponentialProfile_character_apply]
  exact integral_congr_ae (.of_forall fun k ↦
    congrArg (fun z : ℂ ↦ z * (χ k : ℂ)) (bruhatSobolevProfile_apply m τ hτ f x k))


omit hτ ν in
/-- The genuine tests whose topological support lies strictly in the cutoff. -/
def bruhatSobolevCutoffTests (U : Set ℝ) : Submodule ℂ E where
  carrier := {f | tsupport f.val ⊆ modulatedLog m ⁻¹' U}
  zero_mem' := by change tsupport (0 : G → ℂ) ⊆ _; simp
  add_mem' hf hg := (tsupport_add _ _).trans (union_subset hf hg)
  smul_mem' c _ hf := (tsupport_smul_subset_right (fun _ : G ↦ c) _).trans hf

/-- Send supported Bruhat tests to the supported subspace of the weighted
Haar completion with their original pointwise realizations. -/
def bruhatSobolevCutoffInclusion (b : ℝ) (N : ℕ) (U : Set ℝ) :
    bruhatSobolevCutoffTests m U →L[ℂ] modulatedGroupCutoff m τ hτ ν b (2 * (N : ℝ)) U :=
  ((bruhatSobolevInclusion m τ hτ ν b N).comp (bruhatSobolevCutoffTests m U).subtypeL).codRestrict _
    (fun f ↦ (modulatedGroupCutoff_mem_iff m τ hτ ν b (2 * (N : ℝ)) U _).mpr
      ((bruhatSobolevInclusion_ae m τ hτ ν b N f.val).mono fun _ hg hU ↦
        hg.trans (image_eq_zero_of_notMem_tsupport (fun h ↦ hU (f.property h)))))

set_option maxHeartbeats 1700000 in
private theorem separatedTest_mem_bruhatCutoffRange (hm : IsProperMap m) (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U) (χ : PontryaginDual K) (f : compactRadialTests U) :
    modulatedGroupSeparatedTest m τ hτ ν b (2 * (N : ℝ)) hU χ f ∈
      range (bruhatSobolevCutoffInclusion m τ hτ ν b N U) := by
  obtain ⟨j, hj, _⟩ := exists_modulatedExponentialRadialIsotype m τ hτ χ⁻¹ hm
  let u : E := (j f.val).val
  let e := modulatedLogSplit m τ hτ
  have hχ (x : ℝ) (k : K) :
      ((extendModulatedCharacter m τ hτ χ⁻¹ (e (x, k)))⁻¹ : Circle) = χ k := by
    change ((χ⁻¹) (e.symm (e (x, k))).2)⁻¹ = χ k
    rw [e.symm_apply_apply]
    change ((χ k)⁻¹)⁻¹ = χ k
    exact inv_inv _
  have hu (x : ℝ) (k : K) : u.val (e (x, k)) = (χ k : ℂ) * f.val.val x := by
    have h := hj f.val (e (x, k))
    change u.val (e (x, k)) = _ at h
    have hx : (m (e (x, k))).toAdd = x := congrArg Prod.fst (e.symm_apply_apply (x, k))
    exact h.trans ((congrArg₂ (· * ·) (congrArg f.val.val hx)
      (congrArg (fun z : Circle ↦ (z : ℂ)) (hχ x k))).trans (mul_comm _ _))
  obtain ⟨g, _, hg, hgs, hAE⟩ :=
    modulatedGroupSeparatedTest_compactProfile m τ hτ ν b (2 * (N : ℝ)) hU χ f
  have he : u.val = (g : G → ℂ) := by
    funext y
    obtain ⟨⟨x, k⟩, rfl⟩ := e.surjective y
    exact (hu x k).trans (hgs x k).symm
  let v : bruhatSobolevCutoffTests m U := ⟨u, by
    change tsupport u.val ⊆ modulatedLog m ⁻¹' U
    rw [he]
    exact hg⟩
  refine ⟨v, Subtype.ext ?_⟩
  let J := modulatedSobolevGroupEquiv m τ hτ ν b (2 * (N : ℝ))
  apply J.injective
  apply Lp.ext
  have hMP : MeasurePreserving e ((stripMeasure b b (2 * (N : ℝ))).prod ν)
      (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))) :=
    ⟨e.continuous.measurable, rfl⟩
  have hV := (hMP.comp Measure.measurePreserving_swap).quasiMeasurePreserving.ae
    (bruhatSobolevInclusion_ae m τ hτ ν b N u)
  filter_upwards [modulatedSobolevGroupEquiv_ae m τ hτ ν b (2 * (N : ℝ))
      (bruhatSobolevInclusion m τ hτ ν b N u),
    modulatedSobolevGroupEquiv_ae m τ hτ ν b (2 * (N : ℝ))
      (modulatedGroupSeparatedTest m τ hτ ν b (2 * (N : ℝ)) hU χ f).val,
    hV, hAE] with p hleft hright hp hq
  exact hleft.trans (hp.trans ((congrFun he _).trans (hq.symm.trans hright.symm)))

/-- Actual Schwartz–Bruhat tests with strict support are dense in the
physical weighted cutoff subspace. -/
theorem bruhatSobolevCutoff_dense [ν.WeaklyRegular] (hm : IsProperMap m) (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U) :
    DenseRange (bruhatSobolevCutoffInclusion m τ hτ ν b N U) := by
  let L := bruhatSobolevCutoffInclusion m τ hτ ν b N U
  have hsub : Submodule.span ℂ (range (fun p : PontryaginDual K × compactRadialTests U ↦
      modulatedGroupSeparatedTest m τ hτ ν b (2 * (N : ℝ)) hU p.1 p.2)) ≤ L.toLinearMap.range :=
    Submodule.span_le.mpr (by
      rintro _ ⟨⟨χ, f⟩, rfl⟩
      exact separatedTest_mem_bruhatCutoffRange m τ hτ ν hm b N hU χ f)
  have hclosure := Submodule.topologicalClosure_mono hsub
  rw [modulatedGroupSeparatedTest_dense m τ hτ ν b (2 * (N : ℝ)) hU] at hclosure
  exact dense_iff_closure_eq.mpr (congrArg SetLike.coe (top_le_iff.mp hclosure))


/-- The physical cutoff is exactly the ambient closure of the original
strict-support Bruhat tests. -/
theorem bruhatSobolevCutoff_closure [ν.WeaklyRegular] (hm : IsProperMap m) (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatSobolevCutoffTests m U ↦
      bruhatSobolevInclusion m τ hτ ν b N f.val)) =
      (modulatedGroupCutoff m τ hτ ν b (2 * (N : ℝ)) U : Set (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))))) := by
  let T := modulatedGroupCutoff m τ hτ ν b (2 * (N : ℝ)) U
  let J := bruhatSobolevCutoffInclusion m τ hτ ν b N U
  have hT : IsClosed (T : Set (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))))) := by
    rw [← modulatedGroupProfile_cutoffClosure m τ hτ ν b N hU]
    exact isClosed_closure
  have hEmb : IsClosedEmbedding ((↑) : T → (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))))) := hT.isClosedEmbedding_subtypeVal
  change closure (range ((↑) ∘ J : _ → (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ)))))) = _
  rw [range_comp, hEmb.closure_image_eq, (bruhatSobolevCutoff_dense m τ hτ ν hm b N hU).closure_range,
    image_univ, Subtype.range_coe]

/-- The full weighted Haar space is the completion of the original tests. -/
theorem bruhatSobolevInclusion_dense [ν.WeaklyRegular] (hm : IsProperMap m) (b : ℝ) (N : ℕ) :
    DenseRange (bruhatSobolevInclusion m τ hτ ν b N) := by
  have h := bruhatSobolevCutoff_closure m τ hτ ν hm b N isOpen_univ
  have ht : (modulatedGroupCutoff m τ hτ ν b (2 * (N : ℝ)) univ : Set (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))))) = univ := by
    apply eq_univ_of_forall
    intro u
    exact (modulatedGroupCutoff_mem_iff m τ hτ ν b (2 * (N : ℝ)) univ u).mpr
      (.of_forall fun _ h ↦ (h (mem_univ _)).elim)
  rw [ht] at h
  apply dense_iff_closure_eq.mpr
  apply eq_univ_of_univ_subset
  rw [← h]
  apply closure_mono
  rintro _ ⟨f, rfl⟩
  exact ⟨f.val, rfl⟩

/-- Part (1) on the actual strict-support tests, including the indicator
with the closed endpoint used by the manuscript. -/
theorem bruhatSobolev_lowerIndicator [ν.WeaklyRegular] (hm : IsProperMap m) (b : ℝ) (N : ℕ)
    (c : ℝ) :
    let W := modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))
    ∃ P : Lp ℂ 2 W →L[ℂ] Lp ℂ 2 W,
      IsClosed (range P) ∧ (∀ u, P (P u) = P u) ∧
      (∀ u, (P u : G → ℂ) =ᵐ[W] (modulatedLog m ⁻¹' Ici c).indicator (u : G → ℂ)) ∧
      closure (range (fun f : bruhatSobolevCutoffTests m (Ioi c) ↦
        bruhatSobolevInclusion m τ hτ ν b N f.val)) = range P := by
  obtain ⟨P, hclosed, hP, heval, hclosure⟩ :=
    modulatedGroupProfile_lowerIndicator m τ hτ ν b N c
  refine ⟨P, hclosed, hP, heval, ?_⟩
  rw [bruhatSobolevCutoff_closure m τ hτ ν hm b N isOpen_Ioi]
  rw [modulatedGroupProfile_cutoffClosure m τ hτ ν b N isOpen_Ioi] at hclosure
  exact hclosure

end
end Masullo
