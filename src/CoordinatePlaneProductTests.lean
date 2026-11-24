import CoordinatePlaneJetKernel
import CoordinatePlaneRestriction

open Function Set TopologicalSpace Topology WithSeminorms
open scoped ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private abbrev Tests (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  𝓓((⊤ : Opens E), ℂ)

private theorem norm_iteratedFDeriv_comp_contraction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {f : F → ℂ} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

private theorem norm_fst_le_one : ‖ContinuousLinearMap.fst ℝ D V‖ ≤ 1 :=
  (ContinuousLinearMap.fst ℝ D V).opNorm_le_bound zero_le_one fun x ↦ by
    change ‖x.1‖ ≤ 1 * max ‖x.1‖ ‖x.2‖
    rw [one_mul]
    exact le_max_left _ _

private theorem norm_snd_le_one : ‖ContinuousLinearMap.snd ℝ D V‖ ≤ 1 :=
  (ContinuousLinearMap.snd ℝ D V).opNorm_le_bound zero_le_one fun x ↦ by
    change ‖x.2‖ ≤ 1 * max ‖x.1‖ ‖x.2‖
    rw [one_mul]
    exact le_max_right _ _

/-- A Leibniz bound for a separated normal and tangential product. -/
theorem norm_iteratedFDeriv_separated_mul_le
    {φ : D → ℂ} {g : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g)
    (x : D × V) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z : D × V ↦ φ z.1 * g z.2) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i φ x.1‖ * ‖iteratedFDeriv ℝ (n-i) g x.2‖ := by
  let P := ContinuousLinearMap.fst ℝ D V
  let Q := ContinuousLinearMap.snd ℝ D V
  apply (norm_iteratedFDeriv_mul_le (hφ.comp P.contDiff) (hg.comp Q.contDiff) x
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_comp_contraction P norm_fst_le_one hφ i x) (by positivity))
    (norm_iteratedFDeriv_comp_contraction Q norm_snd_le_one hg (n-i) x)
    (norm_nonneg _) (by positivity)

private def productSupport (φ : Tests D) (K : Compacts V) : Compacts (D × V) :=
  ⟨tsupport φ ×ˢ (K : Set V), φ.hasCompactSupport.prod K.isCompact⟩

private def productTestSupported (φ : Tests D) (K : Compacts V) :
    𝓓_{K}(V, ℂ) →ₗ[ℂ] 𝓓_{productSupport φ K}(D × V, ℂ) where
  toFun g := ContDiffMapSupportedIn.of_support_subset
    ((φ.contDiff.comp contDiff_fst).mul (g.contDiff.comp contDiff_snd)) fun x hx ↦ by
      obtain ⟨hφ, hg⟩ := mul_ne_zero_iff.mp hx
      exact ⟨subset_tsupport φ hφ, g.support_subset hg⟩
  map_add' g h := by ext z; exact mul_add _ _ _
  map_smul' a g := by
    ext z
    change φ z.1 * (a * g z.2) = a * (φ z.1 * g z.2)
    ring

private theorem productTestSupported_continuous (φ : Tests D) (K : Compacts V) :
    Continuous (productTestSupported φ K) := by
  let W := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  let C (n : ℕ) : ℝ :=
    ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i W
  have hC (n : ℕ) : 0 ≤ C n := by dsimp [C]; positivity
  refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (ContDiffMapSupportedIn.withSeminorms ..) _
    (fun n ↦ ⟨Finset.range (n+1), (C n).toNNReal, fun g ↦ ?_⟩)
  simp only [Seminorm.comp_apply, smul_apply, NNReal.smul_def, Real.coe_toNNReal _ (hC n)]
  rw [smul_eq_mul, ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (by positivity)]
  intro x _
  change ‖iteratedFDeriv ℝ n (fun z : D × V ↦ φ z.1 * g z.2) x‖ ≤ _
  apply (norm_iteratedFDeriv_separated_mul_le φ.contDiff g.contDiff x n).trans
  dsimp [C]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hni : n-i ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ W i x.1)
      (by positivity))
    (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ |>.trans
      (Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℂ V ℂ ⊤ K) hni |>
        fun h ↦ show _ ≤ _ from h g))
    (norm_nonneg _) (by positivity)

/-- For a fixed normal test, multiplication by a tangential test is
continuous into the compactly supported tests on the product. -/
def testProductLeft (φ : Tests D) : Tests V →L[ℂ] Tests (D × V) :=
  TestFunction.limitCLM ℂ
    (fun g ↦ ⟨fun z ↦ φ z.1 * g z.2,
      (φ.contDiff.comp contDiff_fst).mul (g.contDiff.comp contDiff_snd),
      (productTestSupported φ ⟨tsupport g, g.hasCompactSupport⟩
        (ContDiffMapSupportedIn.of_support_subset g.contDiff subset_closure)).hasCompactSupport,
      subset_univ _⟩)
    (fun K _ ↦ (TestFunction.ofSupportedInCLM ℂ (Ω := ⊤)
      (K := productSupport φ K) (subset_univ _)).comp
      ⟨productTestSupported φ K, productTestSupported_continuous φ K⟩)
    (fun _ _ _ ↦ by ext; rfl)

@[simp] theorem testProductLeft_apply (φ : Tests D) (g : Tests V) (z : D × V) :
    testProductLeft φ g z = φ z.1 * g z.2 := rfl

theorem tsupport_testProductLeft_subset (φ : Tests D) (g : Tests V) :
    tsupport (testProductLeft φ g) ⊆ tsupport φ ×ˢ tsupport g := by
  apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
  intro z hz
  obtain ⟨hφ, hg⟩ := mul_ne_zero_iff.mp (show φ z.1 * g z.2 ≠ 0 from hz)
  exact ⟨subset_tsupport φ hφ, subset_tsupport g hg⟩

/-- The normal jet of a separated test is the jet of its normal factor
times the value of the tangential factor. -/
theorem testProductLeft_normalJet (φ : Tests D) (g : Tests V) (y : V) (n : ℕ) (m : Fin n → D) :
    iteratedFDeriv ℝ n (testProductLeft φ g : D × V → ℂ) (0, y)
        (fun j ↦ (m j, 0)) = iteratedFDeriv ℝ n (φ : D → ℂ) 0 m * g y := by
  let F := (testProductLeft φ g : D × V → ℂ)
  let A := ContinuousLinearMap.inl ℝ D V
  let H : D × V → ℂ := fun z ↦ F (z + (0, y))
  have hH : ContDiff ℝ ∞ H :=
    (testProductLeft φ g).contDiff.comp (contDiff_id.add contDiff_const)
  have htop : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  calc
    _ = iteratedFDeriv ℝ n H 0 (A ∘ m) := by
      rw [show H = fun z ↦ F (z + (0, y)) from rfl, iteratedFDeriv_comp_add_right, zero_add]
      rfl
    _ = iteratedFDeriv ℝ n (H ∘ A) 0 m := by
      rw [A.iteratedFDeriv_comp_right hH 0 htop, map_zero]
      rfl
    _ = _ := by
      have he : H ∘ A = fun z ↦ g y • φ z := by
        funext z
        simp [H, A, F, smul_eq_mul, mul_comm]
      rw [he, iteratedFDeriv_const_smul_apply' (φ.contDiff.of_le htop).contDiffAt,
        smul_apply, smul_eq_mul, mul_comm]

end
end Masullo
