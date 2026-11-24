import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.Basic

open Filter Function Set TopologicalSpace Topology WithSeminorms
open scoped ContDiff Distributions

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_mul_of_tsupport_subset {Ω : Opens E}
    {φ f : E → ℂ} (hφ : ContDiffOn ℝ ∞ φ (Ω : Set E))
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ (Ω : Set E)) :
    ContDiff ℝ ∞ (fun x ↦ φ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ (Ω : Set E)
  · exact (hφ.contDiffAt (Ω.isOpen.mem_nhds hx)).mul hf.contDiffAt
  · have he : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hs h))
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (by
      filter_upwards [he] with y hy
      simp [hy])

private def stageTestMultiplier {Ω : Opens E} {φ : E → ℂ}
    (hφ : ContDiffOn ℝ ∞ φ (Ω : Set E))
    (K : Compacts E) (hK : (K : Set E) ⊆ (Ω : Set E)) :
    𝓓_{K}(E, ℂ) →ₗ[ℂ] 𝓓_{K}(E, ℂ) where
  toFun f := ContDiffMapSupportedIn.of_support_subset
    (contDiff_mul_of_tsupport_subset hφ f.contDiff (f.tsupport_subset.trans hK))
    (fun _ hx ↦ f.support_subset ((mul_ne_zero_iff.mp hx).2))
  map_add' _ _ := by ext x; exact mul_add _ _ _
  map_smul' a f := by
    ext x
    change φ x * (a * f x) = a * (φ x * f x)
    ring

private theorem stageTestMultiplier_continuous {Ω : Opens E} {φ : E → ℂ}
    (hφ : ContDiffOn ℝ ∞ φ (Ω : Set E))
    (K : Compacts E) (hK : (K : Set E) ⊆ (Ω : Set E)) :
    Continuous (stageTestMultiplier hφ K hK) := by
  classical
  have hΩ : UniqueDiffOn ℝ (Ω : Set E) := Ω.isOpen.uniqueDiffOn
  have htop (i : ℕ) : (i : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤)
  have hb (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ (K : Set E), ‖iteratedFDerivWithin ℝ i φ (Ω : Set E) x‖ ≤ B := by
    have hc := (hφ.continuousOn_iteratedFDerivWithin (htop i) hΩ).norm.mono hK
    obtain ⟨r, hr⟩ := K.isCompact.bddAbove_image hc
    exact ⟨max r 0, le_max_right _ _, fun x hx ↦ (hr ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hb using hb
  let C (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B i
  have hC (n : ℕ) : 0 ≤ C n := by
    dsimp only [C]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (hB i)
  refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (ContDiffMapSupportedIn.withSeminorms ..) _
    (fun n ↦ ⟨Finset.range (n+1), (C n).toNNReal, fun f ↦ ?_⟩)
  simp only [Seminorm.comp_apply, smul_apply, NNReal.smul_def, Real.coe_toNNReal _ (hC n)]
  rw [smul_eq_mul, ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (mul_nonneg (hC n) (apply_nonneg _ _))]
  intro x hx
  change ‖iteratedFDeriv ℝ n (fun y ↦ φ y * f y) x‖ ≤ _
  rw [← iteratedFDerivWithin_of_isOpen n Ω.isOpen (hK hx)]
  apply (norm_iteratedFDerivWithin_mul_le hφ f.contDiff.contDiffOn hΩ (hK hx) (htop n)).trans
  dsimp only [C]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [iteratedFDerivWithin_of_isOpen (n-i) Ω.isOpen (hK hx)]
  have hni : n-i ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i x hx) (by positivity))
    (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ |>.trans
      (Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K) hni |>
        fun h ↦ Seminorm.le_def.mp h f)) (norm_nonneg _) (mul_nonneg (by positivity) (hB i))

/-- Multiplication by a function smooth on the open domain is continuous
for the full compact-test LF topology, including domains with punctures. -/
def openTestMultiplier (Ω : Opens E) (φ : E → ℂ)
    (hφ : ContDiffOn ℝ ∞ φ (Ω : Set E)) : 𝓓(Ω, ℂ) →L[ℂ] 𝓓(Ω, ℂ) :=
  TestFunction.limitCLM ℂ
    (fun f ↦ ⟨fun x ↦ φ x * f x,
      contDiff_mul_of_tsupport_subset hφ f.contDiff f.tsupport_subset,
      f.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right,
      tsupport_mul_subset_right.trans f.tsupport_subset⟩)
    (fun K hK ↦ (TestFunction.ofSupportedInCLM ℂ hK).comp
      ⟨stageTestMultiplier hφ K hK, stageTestMultiplier_continuous hφ K hK⟩)
    (fun _ _ _ ↦ by ext; rfl)

@[simp] theorem openTestMultiplier_apply (Ω : Opens E) (φ : E → ℂ)
    (hφ : ContDiffOn ℝ ∞ φ (Ω : Set E)) (f : 𝓓(Ω, ℂ)) (x : E) :
    openTestMultiplier Ω φ hφ f x = φ x * f x := rfl

/-- A smooth multiplier that has no zeros on the open domain gives a
continuous linear automorphism of compact tests, with reciprocal inverse. -/
def openTestMultiplierEquiv (Ω : Opens E) (φ : E → ℂ)
    (hφ : ContDiffOn ℝ ∞ φ (Ω : Set E)) (hn : ∀ x ∈ (Ω : Set E), φ x ≠ 0) :
    𝓓(Ω, ℂ) ≃L[ℂ] 𝓓(Ω, ℂ) := by
  let A := openTestMultiplier Ω φ hφ
  let B := openTestMultiplier Ω (fun x ↦ (φ x)⁻¹) (hφ.inv hn)
  refine ContinuousLinearEquiv.equivOfInverse A B ?_ ?_
  all_goals
    intro f
    ext x
    by_cases hx : x ∈ (Ω : Set E)
    · simp [A, B, hn x hx]
    · have hz := image_eq_zero_of_notMem_tsupport (f := (f : E → ℂ))
        (fun hs ↦ hx (f.tsupport_subset hs))
      simp [A, B, hz]

/-- The standard punctured additive domain, used for compact tests
on multiplicative real or complex groups. -/
def puncturedOpens (E : Type*) [NormedAddCommGroup E] : Opens E :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

/-- Coordinate multiplication on compact tests on the punctured real line. -/
def realPuncturedTestMul : 𝓓(puncturedOpens ℝ, ℂ) ≃L[ℂ] 𝓓(puncturedOpens ℝ, ℂ) :=
  openTestMultiplierEquiv _ Complex.ofReal Complex.ofRealCLM.contDiff.contDiffOn
    (fun _ hx ↦ Complex.ofReal_ne_zero.mpr hx)

/-- Coordinate multiplication on compact tests on the punctured complex plane. -/
def complexPuncturedTestMul : 𝓓(puncturedOpens ℂ, ℂ) ≃L[ℂ] 𝓓(puncturedOpens ℂ, ℂ) :=
  openTestMultiplierEquiv _ id contDiff_id.contDiffOn (fun _ hx ↦ hx)

/-- Conjugate coordinate multiplication on compact tests on the punctured complex plane. -/
def complexPuncturedTestConjMul : 𝓓(puncturedOpens ℂ, ℂ) ≃L[ℂ] 𝓓(puncturedOpens ℂ, ℂ) :=
  openTestMultiplierEquiv _ (starRingEnd ℂ) Complex.conjCLE.contDiff.contDiffOn
    (fun _ hx ↦ (map_ne_zero _).2 hx)

@[simp] theorem realPuncturedTestMul_apply (f : 𝓓(puncturedOpens ℝ, ℂ)) (x : ℝ) :
    realPuncturedTestMul f x = (x : ℂ) * f x := rfl

@[simp] theorem complexPuncturedTestMul_apply (f : 𝓓(puncturedOpens ℂ, ℂ)) (z : ℂ) :
    complexPuncturedTestMul f z = z * f z := rfl

@[simp] theorem complexPuncturedTestConjMul_apply (f : 𝓓(puncturedOpens ℂ, ℂ)) (z : ℂ) :
    complexPuncturedTestConjMul f z = (starRingEnd ℂ) z * f z := rfl

private abbrev ComplexTests := 𝓓(puncturedOpens ℂ, ℂ)

private def complexTestDirection (v : ℂ) : ComplexTests →L[ℂ] ComplexTests :=
  TestFunction.lineDerivCLM ℂ v

private theorem complexTestDirection_apply (v z : ℂ) (f : ComplexTests) :
    complexTestDirection v f z = fderiv ℝ (f : ℂ → ℂ) z v := by
  rw [complexTestDirection, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, ite_eq_left le_top]

private def complexTestConstantMul (a : ℂ) : ComplexTests →L[ℂ] ComplexTests :=
  openTestMultiplier _ (fun _ ↦ a) contDiff_const.contDiffOn

/-- Ordinary Wirtinger differentiation on punctured complex compact tests. -/
def complexPuncturedTestWirtingerZ : ComplexTests →L[ℂ] ComplexTests :=
  (complexTestConstantMul (1 / 2)).comp
    (complexTestDirection 1 - (complexTestConstantMul Complex.I).comp (complexTestDirection Complex.I))

/-- Conjugate Wirtinger differentiation on punctured complex compact tests. -/
def complexPuncturedTestWirtingerBar : ComplexTests →L[ℂ] ComplexTests :=
  (complexTestConstantMul (1 / 2)).comp
    (complexTestDirection 1 + (complexTestConstantMul Complex.I).comp (complexTestDirection Complex.I))

@[simp] theorem complexPuncturedTestWirtingerZ_apply (f : ComplexTests) (z : ℂ) :
    complexPuncturedTestWirtingerZ f z =
      (1 / 2 : ℂ) * (fderiv ℝ (f : ℂ → ℂ) z 1 - Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I) := by
  change (1 / 2 : ℂ) * (complexTestDirection 1 f z - Complex.I * complexTestDirection Complex.I f z) = _
  rw [complexTestDirection_apply, complexTestDirection_apply]

@[simp] theorem complexPuncturedTestWirtingerBar_apply (f : ComplexTests) (z : ℂ) :
    complexPuncturedTestWirtingerBar f z =
      (1 / 2 : ℂ) * (fderiv ℝ (f : ℂ → ℂ) z 1 + Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I) := by
  change (1 / 2 : ℂ) * (complexTestDirection 1 f z + Complex.I * complexTestDirection Complex.I f z) = _
  rw [complexTestDirection_apply, complexTestDirection_apply]

end
end Masullo
