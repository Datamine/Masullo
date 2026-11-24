/-
The basis estimates adapt RiemannMasullo Ch04_PeriodicSchauderBases/Sec1.lean at
db376192baf52253727c46e2b211619d4e6a3941 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import AbsoluteBasisDuality
import NuclearPermanence
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open Filter Function Set Topology ContinuousLinearMap
open scoped NNReal TensorProduct PointwiseConvergenceCLM

namespace Masullo
open InjectiveTensorTools

noncomputable section

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Nuclearity bounds finite sums of a seminorm by the common weak absolute
sum bound for the polar of one larger continuous seminorm. -/
private theorem nuclear_finite_sum_bound
    (hE : NuclearLocallyConvex.{max u v, u} E) (s : Seminorm ℂ E) (hs : Continuous s) :
    ∃ (p : Seminorm ℂ E) (A : ℝ), Continuous p ∧ s ≤ p ∧ 0 ≤ A ∧
      ∀ (n : ℕ) (z : Fin n → E) (B : ℝ), 0 ≤ B →
        (∀ φ : StrongDual ℂ E, (∀ x, ‖φ x‖ ≤ p x) → ∑ i, ‖φ (z i)‖ ≤ B) →
        ∑ i, s (z i) ≤ A * B := by
  letI : PolynormableSpace ℂ E := hE.2.1
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let Y := ULift.{v} (StrongDual ℂ (LocalBanach s))
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let j := localBanachMap s hs
  let b : E →ₗ[ℂ] Y →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x y => y.down (j x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  have hb : Continuous (fun z : E × Y => b z.1 z.2) :=
    (ContinuousLinearMap.apply ℂ (E := LocalBanach s) ℂ).continuous₂.comp
      ((j.continuous.comp continuous_fst).prodMk (continuous_uliftDown.comp continuous_snd))
  let l := TensorProduct.lift b
  have hl := continuous_projectiveTensor_lift b hb
  rw [hE.2.2 Y] at hl
  have hln : Continuous[injectiveTensorTopology E Y, _] ((normSeminorm ℂ ℂ).comp l) := by
    letI : TopologicalSpace (E ⊗[ℂ] Y) := injectiveTensorTopology E Y
    exact hl.norm
  obtain ⟨I, hI⟩ := continuous_injectiveTensor_seminorm_domination _ hln
  let P := injectiveAsProjectiveTest I
  let p := s ⊔ P.first
  obtain ⟨J, A, _, hA⟩ := Seminorm.bound_of_continuous (norm_withSeminorms ℂ Y)
    P.second P.second_continuous
  have hA' (y : Y) : P.second y ≤ (A : ℝ) * ‖y‖ :=
    (hA y).trans (mul_le_mul_of_nonneg_left
      (show (J.sup (fun _ => normSeminorm ℂ Y)) y ≤ ‖y‖ from
        (Finset.sup_le (fun _ _ => le_rfl : ∀ a ∈ J, normSeminorm ℂ Y ≤ normSeminorm ℂ Y)) y)
      A.coe_nonneg)
  refine ⟨p, A, hs.sup P.first_continuous, le_sup_left, A.coe_nonneg, ?_⟩
  intro n z B hB htest
  choose ψ hψ hψz using fun i : Fin n => exists_dual_vector'' ℂ (j (z i))
  let y (i : Fin n) : Y := ULift.up (ψ i)
  let t := ∑ i, z i ⊗ₜ[ℂ] y i
  have hval : l t = (↑(∑ i, s (z i)) : ℂ) := by
    rw [map_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change TensorProduct.lift b (z i ⊗ₜ[ℂ] y i) = _
    rw [TensorProduct.lift.tmul]
    change ψ i (j (z i)) = _
    rw [hψz i, show ‖j (z i)‖ = s (z i) from norm_localBanachDenseMap s _]
    rfl
  calc
    ∑ i, s (z i) = ‖l t‖ := by rw [hval, Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)]
    _ ≤ injectiveTensorSeminorm I t := hI t
    _ ≤ (A : ℝ) * B := by
      apply injectiveTensorSeminorm_le _ _ _ (mul_nonneg A.coe_nonneg hB)
      intro φ hφ ξ hξ
      change ‖dualPair φ ξ (∑ i, z i ⊗ₜ[ℂ] y i)‖ ≤ _
      rw [map_sum]
      refine (norm_sum_le _ _).trans ?_
      simp only [dualPair_tmul, norm_mul]
      calc
        ∑ i, ‖φ (z i)‖ * ‖ξ (y i)‖ ≤ ∑ i, ‖φ (z i)‖ * A := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (dualTestSeminorm_dom I.2 ⟨ξ, hξ⟩ _).trans ((hA' _).trans
            (mul_le_of_le_one_right A.coe_nonneg (hψ i)))
        _ ≤ (A : ℝ) * B := by
          rw [← Finset.sum_mul, mul_comm (A : ℝ)]
          exact mul_le_mul_of_nonneg_right
            (htest (show StrongDual ℂ E from φ) fun x =>
              (dualTestSeminorm_dom I.1 ⟨φ, hφ⟩ x).trans ((le_sup_right : P.first ≤ p) x))
            A.coe_nonneg

section EquicontinuousBasis

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable (x : ℕ → E) (f : ℕ → StrongDual ℂ E)

/-- Partial coordinate projection through index k. -/
def basisPartialProjection (k : ℕ) : E →L[ℂ] E :=
  ∑ m ∈ Finset.Iic k, (f m).smulRight (x m)

/-- Equicontinuity of the partial coordinate projections. -/
def IsEquicontinuousBasis : Prop :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  EquicontinuousAt (fun k ↦ (basisPartialProjection x f k : E → E)) 0

variable {x f}
/-- Equicontinuity of the partial projections bounds all individual coordinate
projections by a common continuous seminorm. -/
private theorem exists_coordinate_seminorm_bound [PolynormableSpace ℂ E] (heq : IsEquicontinuousBasis x f)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ p : Seminorm ℂ E, Continuous p ∧ ∀ n z, q (f n z • x n) ≤ p z := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let G (k : ℕ) : E →ₗ[ℂ] E := (basisPartialProjection x f k).toLinearMap
  have hG : UniformEquicontinuous ((↑) ∘ G) :=
    uniformEquicontinuous_of_equicontinuousAt_zero G heq
  obtain ⟨p, hp, hbound⟩ :=
    ((PolynormableSpace.withSeminorms ℂ E).uniformEquicontinuous_iff_exists_continuous_seminorm
      G).mp hG ⟨q, hq⟩
  have hproj (k : ℕ) (z : E) :
      basisPartialProjection x f k z = ∑ m ∈ Finset.range (k + 1), f m z • x m := by
    rw [basisPartialProjection, ← Nat.range_succ_eq_Iic]
    simp [sum_apply, ContinuousLinearMap.smulRight_apply]
  have hle (k : ℕ) (z : E) : q (basisPartialProjection x f k z) ≤ p z := hbound k z
  refine ⟨(2 : NNReal) • p, hp.const_smul _, fun n z ↦ ?_⟩
  change q (f n z • x n) ≤ 2 * p z
  cases n with
  | zero =>
    have h := hle 0 z
    rw [hproj] at h
    exact (by simpa using h : q (f 0 z • x 0) ≤ p z).trans (by linarith [apply_nonneg p z])
  | succ n =>
    have hstep : f (n + 1) z • x (n + 1) =
        basisPartialProjection x f (n + 1) z - basisPartialProjection x f n z := by
      rw [hproj, hproj, Finset.sum_range_succ, add_sub_cancel_left]
    rw [hstep]
    exact (map_sub_le_add q _ _).trans (by linarith [hle (n + 1) z, hle n z])

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
open InnerProductSpace in
/-- Gram–Schmidt on the images of the basis admits lifts that retain their own
basis coefficient. The residual images have norm at most that of the original images. -/
private theorem exists_orthogonal_coordinate_lifts
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : E →ₗ[ℂ] H) (hb : IsSchauderBasis x f) :
    ∃ y : ℕ → E, (∀ i, f i (y i) = 1) ∧ (∀ i, ‖a (y i)‖ ≤ ‖a (x i)‖) ∧
      Pairwise (fun i j ↦ inner ℂ (a (y i)) (a (y j)) = 0) := by
  let b := gramSchmidt ℂ (a ∘ x)
  have hspan (i : ℕ) : b i ∈ (Submodule.span ℂ (x '' Iic i)).map a := by
    rw [Submodule.map_span, image_image]
    exact gramSchmidt_mem_span ℂ _ le_rfl
  choose v hv hmap using fun i ↦ Submodule.mem_map.mp (hspan i)
  let c (i j : ℕ) : ℂ := inner ℂ (b j) (a (x i)) / (‖b j‖ : ℂ)^2
  let y (i : ℕ) : E := x i - ∑ j ∈ Finset.Iio i, c i j • v j
  have heq (i : ℕ) : a (y i) = b i := by
    simp only [y, map_sub, map_sum, map_smul, hmap]
    conv_lhs => rw [show a (x i) = (a ∘ x) i from rfl, gramSchmidt_def'' ℂ (a ∘ x) i]
    change b i + (∑ j ∈ Finset.Iio i, c i j • b j) -
      (∑ j ∈ Finset.Iio i, c i j • b j) = b i
    exact add_sub_cancel_right _ _
  refine ⟨y, ?_, ?_, fun i j hij ↦ by
    simpa only [heq] using gramSchmidt_pairwise_orthogonal ℂ (a ∘ x) hij⟩
  · intro i
    have hzero (j : ℕ) (hj : j < i) : f i (v j) = 0 := by
      have hle : Submodule.span ℂ (x '' Iic j) ≤ (f i).toLinearMap.ker := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨k, hk, rfl⟩
        exact LinearMap.mem_ker.mpr (by
          rw [show (f i).toLinearMap (x k) = if i = k then 1 else 0 from hb.1 i k]
          exact ite_eq_right (ne_of_gt ((mem_Iic.mp hk).trans_lt hj)))
      exact hle (hv j)
    have hdiag : f i (x i) = 1 := by simpa using hb.1 i i
    simp only [y, map_sub, map_sum, map_smul, hdiag]
    rw [Finset.sum_eq_zero, sub_zero]
    exact fun j hj ↦ by rw [hzero j (Finset.mem_Iio.mp hj), smul_zero]
  · intro i
    rw [heq]
    have hinner : inner ℂ (b i) (a (x i)) = inner ℂ (b i) (b i) := by
      conv_lhs => rw [show a (x i) = (a ∘ x) i from rfl, gramSchmidt_def'' ℂ (a ∘ x) i]
      change inner ℂ (b i) (b i + ∑ j ∈ Finset.Iio i, c i j • b j) = _
      rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
      exact fun j hj ↦ by
        rw [inner_smul_right,
          gramSchmidt_pairwise_orthogonal ℂ (a ∘ x) (ne_of_gt (Finset.mem_Iio.mp hj)),
          mul_zero]
    have h := norm_inner_le_norm (𝕜 := ℂ) (b i) (a (x i))
    rw [hinner, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
    change ‖((‖b i‖ ^ 2 : ℝ) : ℂ)‖ ≤ _ at h
    rw [Complex.norm_of_nonneg (sq_nonneg _), pow_two] at h
    by_cases hi : ‖b i‖ = 0
    · simp [hi]
    · exact le_of_mul_le_mul_left h (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi))

open InnerProductSpace UniformSpace in
/-- Nuclearity gives a continuous denominator seminorm for which the ratios of
basis-vector seminorms have uniformly bounded finite sums of squares. -/
private theorem exists_square_summable_coordinate_ratios (hE : NuclearLocallyConvex.{max u v, u} E)
    (hb : IsSchauderBasis x f) (heq : IsEquicontinuousBasis x f)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (r : Seminorm ℂ E) (C : ℝ), Continuous r ∧ 0 ≤ C ∧
      (∀ i, r (x i) = 0 → q (x i) = 0) ∧
      ∀ n, (∑ i ∈ Finset.range n, (q (x i) / r (x i)) ^ 2) ≤ C ^ 2 := by
  let := hE.2.1
  obtain ⟨s, hs, hscoord⟩ := exists_coordinate_seminorm_bound heq q hq
  obtain ⟨p, A, hpc, hsp, hA, hsum⟩ := nuclear_finite_sum_bound hE s hs
  obtain ⟨H, _, _, _, a, D, hD, hp⟩ := nuclearLocallyConvex_hilbert_domination hE p hpc
  let r := (normSeminorm ℂ H).comp a.toLinearMap
  obtain ⟨y, hycoef, hynorm, hyorth⟩ := exists_orthogonal_coordinate_lifts a.toLinearMap hb
  have hzero (i : ℕ) (hi : r (x i) = 0) : q (x i) = 0 := by
    have hdiag : f i (x i) = 1 := by simpa using hb.1 i i
    have h₁ : q (x i) ≤ s (x i) := by simpa only [hdiag, one_smul] using hscoord i (x i)
    have h₂ : s (x i) ≤ p (x i) := hsp (x i)
    have h₃ : p (x i) ≤ 0 := by
      have h := hp (x i)
      change p (x i) ≤ D * r (x i) at h
      simpa only [hi, mul_zero] using h
    exact le_antisymm (h₁.trans (h₂.trans h₃)) (apply_nonneg _ _)
  refine ⟨r, A * D, a.continuous.norm, mul_nonneg hA hD, hzero, fun n ↦ ?_⟩
  let b (i : Fin n) := q (x i) / r (x i)
  -- Normalize the orthogonal lifts by the seminorms of the original basis vectors.
  let w (i : Fin n) : E := (↑((r (x i))⁻¹) : ℂ) • y i
  have hw (i : Fin n) : ‖a (w i)‖ ≤ 1 := by
    have hn : 0 ≤ r (x i) := apply_nonneg _ _
    change ‖a ((↑((r (x i))⁻¹) : ℂ) • y i)‖ ≤ 1
    rw [map_smul, norm_smul, Complex.norm_of_nonneg (inv_nonneg.mpr hn)]
    refine (mul_le_mul_of_nonneg_left (hynorm i) (inv_nonneg.mpr hn)).trans ?_
    change (r (x i))⁻¹ * r (x i) ≤ 1
    by_cases hi : r (x i) = 0 <;> simp [hi]
  have hbw (i : Fin n) : b i ≤ s (w i) := by
    have hy : q (x i) ≤ s (y i) := by
      simpa only [hycoef, one_smul] using hscoord i (y i)
    calc
      b i = (r (x i))⁻¹ * q (x i) := by
        change (_ / _) = _
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ (r (x i))⁻¹ * s (y i) := mul_le_mul_of_nonneg_left hy (by positivity)
      _ = s (w i) := by
        change _ = s ((↑((r (x i))⁻¹) : ℂ) • y i)
        rw [map_smul_eq_mul, Complex.norm_of_nonneg (by positivity)]
  have horth (i j : Fin n) (hij : i ≠ j) : inner ℂ (a (w i)) (a (w j)) = 0 := by
    simp only [w, map_smul, inner_smul_left, inner_smul_right]
    change _ * (_ * inner ℂ (a (y i)) (a (y j))) = _
    have hz : inner ℂ (a (y i)) (a (y j)) = 0 := hyorth (Fin.val_injective.ne hij)
    rw [hz, mul_zero, mul_zero]
  have hnorm (c : Fin n → ℂ) : ‖a (∑ i, c i • w i)‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2 := by
    rw [map_sum, norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner, map_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [inner_sum, map_sum, Finset.sum_eq_single i]
    · rw [← norm_sq_eq_re_inner (𝕜 := ℂ), map_smul, norm_smul, mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith [hw i, norm_nonneg (a (w i))])
    · intro j _ hij
      simp [inner_smul_left, inner_smul_right, horth i j (Ne.symm hij)]
    · simp
  -- Each dual unit functional has a uniform square-sum bound on the lifts.
  have hdual (φ : StrongDual ℂ E) (hφ : ∀ z, ‖φ z‖ ≤ p z) :
      (∑ i, ‖φ (w i)‖ ^ 2) ≤ D ^ 2 := by
    let c (i : Fin n) := (starRingEnd ℂ) (φ (w i))
    let M : ℝ := ∑ i, ‖φ (w i)‖ ^ 2
    let z : E := ∑ i, c i • w i
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hval : φ z = (M : ℂ) := by
      simp only [z, map_sum, map_smul, smul_eq_mul, c, M, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hle : M ≤ D * ‖a z‖ := by
      have hh := hφ z
      rw [hval, Complex.norm_of_nonneg hM] at hh
      exact hh.trans (hp z)
    have ha : ‖a z‖ ^ 2 ≤ M := by simpa only [z, c, starRingEnd_apply, norm_star] using hnorm c
    have hsq : M ^ 2 ≤ D ^ 2 * M := calc
      M ^ 2 ≤ (D * ‖a z‖) ^ 2 := by gcongr
      _ = D ^ 2 * ‖a z‖ ^ 2 := mul_pow _ _ _
      _ ≤ D ^ 2 * M := by gcongr
    change M ≤ D ^ 2
    by_cases hm : M = 0
    · rw [hm]
      exact sq_nonneg _
    · exact le_of_mul_le_mul_right (by simpa only [pow_two] using hsq)
        (lt_of_le_of_ne hM (Ne.symm hm))
  let M : ℝ := ∑ i, b i ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  let z (i : Fin n) : E := (b i : ℂ) • w i
  have hbnn (i : Fin n) : 0 ≤ b i := div_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  -- Test the absolutely summing map on the lifts weighted by the ratios.
  have hbound : ∑ i, s (z i) ≤ A * (Real.sqrt M * D) := by
    refine hsum n z (Real.sqrt M * D) (mul_nonneg (Real.sqrt_nonneg _) hD) fun φ hφ ↦ ?_
    simp only [z, map_smul, norm_smul, Complex.norm_of_nonneg (hbnn _)]
    exact (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ b (fun i ↦ ‖φ (w i)‖)).trans
      (mul_le_mul_of_nonneg_left ((Real.sqrt_le_iff.mpr ⟨hD, hdual φ hφ⟩)) (Real.sqrt_nonneg _))
  have hle : M ≤ (A * D) * Real.sqrt M := by
    calc
      M ≤ ∑ i, s (z i) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        change b i ^ 2 ≤ s ((b i : ℂ) • w i)
        rw [map_smul_eq_mul, Complex.norm_of_nonneg (hbnn i), pow_two]
        exact mul_le_mul_of_nonneg_left (hbw i) (hbnn i)
      _ ≤ A * (Real.sqrt M * D) := hbound
      _ = (A * D) * Real.sqrt M := by ring
  rw [← Fin.sum_univ_eq_sum_range]
  change M ≤ (A * D) ^ 2
  have hsqrt : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
  have hnonneg := Real.sqrt_nonneg M
  by_cases hz : Real.sqrt M = 0
  · rw [← hsqrt, hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _
  · have hdiv : Real.sqrt M ≤ A * D := by
      have hh : Real.sqrt M * Real.sqrt M ≤ (A * D) * Real.sqrt M :=
        (pow_two _).symm.trans hsqrt |>.le.trans hle
      exact le_of_mul_le_mul_right hh (lt_of_le_of_ne hnonneg (Ne.symm hz))
    rw [← hsqrt]
    gcongr

/-- Paper: Theorem 4.1.2.6(1), p. 161. Every equicontinuous Schauder basis of a
nuclear space is absolute. -/
theorem isAbsolute_of_isNuclearTVS
    (hE : NuclearLocallyConvex.{max u v, u} E) (hb : IsSchauderBasis x f) (heq : IsEquicontinuousBasis x f) :
    IsAbsolute x f := by
  let := hE.2.1
  intro q hq
  obtain ⟨r, A, hr, hA, hqr, hsq₁⟩ :=
    exists_square_summable_coordinate_ratios hE hb heq q hq
  obtain ⟨s, B, hs, hB, hrs, hsq₂⟩ :=
    exists_square_summable_coordinate_ratios hE hb heq r hr
  obtain ⟨p, hp, hcoord⟩ := exists_coordinate_seminorm_bound heq s hs
  let a (i : ℕ) := q (x i) / r (x i)
  let b (i : ℕ) := r (x i) / s (x i)
  -- Two square-summable ratios give a summable ratio by Cauchy–Schwarz.
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, a i * b i ≤ A * B :=
    (Real.sum_mul_le_sqrt_mul_sqrt _ a b).trans
      (mul_le_mul (Real.sqrt_le_iff.mpr ⟨hA, hsq₁ n⟩) (Real.sqrt_le_iff.mpr ⟨hB, hsq₂ n⟩)
        (Real.sqrt_nonneg _) hA)
  have hfactor (i : ℕ) : a i * b i * s (x i) = q (x i) := by
    by_cases hs₀ : s (x i) = 0
    · rw [hs₀, mul_zero, hqr i (hrs i hs₀)]
    by_cases hr₀ : r (x i) = 0
    · simp [a, hqr i hr₀]
    dsimp only [a, b]
    rw [mul_assoc, div_mul_cancel₀ _ hs₀, div_mul_cancel₀ _ hr₀]
  let C : NNReal := ⟨A * B, mul_nonneg hA hB⟩
  refine ⟨C • p, hp.const_smul C, fun z ↦ ?_⟩
  have hbound (n : ℕ) : (∑ i ∈ Finset.range n, q (f i z • x i)) ≤ (C : ℝ) * p z := by
    calc
      _ = ∑ i ∈ Finset.range n, (a i * b i) * s (f i z • x i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [map_smul_eq_mul]
        rw [← hfactor i, mul_left_comm ‖f i z‖, mul_assoc]
      _ ≤ ∑ i ∈ Finset.range n, (a i * b i) * p z := by
        refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hcoord i z) ?_
        dsimp only [a, b]
        positivity
      _ ≤ (C : ℝ) * p z := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hsum n) (apply_nonneg _ _)
  exact ⟨summable_of_sum_range_le (fun _ ↦ apply_nonneg _ _) hbound,
    Real.tsum_le_of_sum_range_le (fun _ ↦ apply_nonneg _ _) hbound⟩


end EquicontinuousBasis

variable {x : ℕ → E} {f : ℕ → StrongDual ℂ E}

/-- Banach–Steinhaus makes every Schauder basis on a barrelled locally convex
space equicontinuous. -/
theorem schauderBasis_equicontinuous_of_barrelled
    [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [ContinuousSMul ℂ E]
    [BarrelledSpace ℂ E] (hb : IsSchauderBasis x f) : IsEquicontinuousBasis x f := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have htend (z : E) : Tendsto (fun k ↦ basisPartialProjection x f k z) atTop (𝓝 z) := by
    have hsum := hb.2 z
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hsum
    simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, basisPartialProjection,
      ← Nat.range_succ_eq_Iic, sum_apply, ContinuousLinearMap.smulRight_apply]
      using hsum.comp (tendsto_add_atTop_nat 1)
  have heq := PolynormableSpace.banach_steinhaus (𝓕 := basisPartialProjection x f)
    (fun z ↦ (htend z).isVonNBounded_range ℂ)
  exact heq.equicontinuous 0

/-- Every Schauder basis of a nuclear Fréchet space is absolute. -/
theorem isAbsolute_of_nuclear_frechet
    (hE : NuclearLocallyConvex.{max u v, u} E) (hFrechet : IsFrechetTVS E)
    (hb : IsSchauderBasis x f) : IsAbsolute x f := by
  let : BarrelledSpace ℂ E := isFrechetTVS_barrelled hFrechet
  obtain ⟨hadd, hpoly, _, _⟩ := hFrechet
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  exact isAbsolute_of_isNuclearTVS hE hb (schauderBasis_equicontinuous_of_barrelled hb)

/-- Every Schauder basis in a strict countable inductive limit of nuclear
Fréchet spaces is absolute. The stages are represented by their images with
the subspace topology. -/
theorem isAbsolute_of_nuclear_strictLF_stages [T2Space E]
    (S : ℕ → Submodule ℂ E) (hS : Monotone S)
    (hFrechet : ∀ n, IsFrechetTVS (S n))
    (hNuclear : ∀ n, NuclearLocallyConvex.{max u v, u} (S n))
    (hexhaustive : ∀ z : E, ∃ n, z ∈ S n)
    (ht : (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology (fun n ↦ (S n).subtype))
    (hb : IsSchauderBasis x f) : IsAbsolute x f := by
  let stageInclusion (n : ℕ) := (S n).subtype
  have hE : WithSeminorms (fun p : FinalSeminorm stageInclusion => p.val) := ⟨ht⟩
  let : PolynormableSpace ℂ E := hE.toPolynormableSpace
  let : IsTopologicalAddGroup E := hE.topologicalAddGroup
  let : ContinuousSMul ℂ E := hE.continuousSMul
  let : ∀ n, IsTopologicalAddGroup (S n) := fun n ↦ (hFrechet n).choose
  have hN : NuclearLocallyConvex.{max u v, u} E := by
    let j (i k : ℕ) (hik : i ≤ k) := Submodule.inclusion (hS hik)
    let : DirectedSystem (fun n ↦ S n) (j · · ·) :=
      ⟨fun {_} _ ↦ rfl, fun {_ _ _} _ _ _ ↦ rfl⟩
    let L := Module.DirectLimit (fun n ↦ S n) j
    let stage := Module.DirectLimit.of ℂ ℕ (fun n ↦ S n) j
    let : TopologicalSpace L := locallyConvexFinalTopology stage
    let g : L →ₗ[ℂ] E := Module.DirectLimit.lift ℂ ℕ (fun n ↦ S n) j
      stageInclusion (fun _ _ _ _ ↦ rfl)
    have hg_stage (n : ℕ) (z : S n) : g (stage n z) = z :=
      Module.DirectLimit.lift_of (G := fun n ↦ S n) (f := j) _ _ z
    have hginj : Function.Injective g :=
      Module.DirectLimit.lift_injective _ _ fun _ ↦ Subtype.val_injective
    have hg : Continuous g :=
      (locallyConvexFinal_continuous_iff stage g).mpr fun n ↦
        continuous_subtype_val.congr (fun z ↦ (hg_stage n z).symm)
    let : T2Space L := T2Space.of_injective_continuous hginj hg
    let e : L ≃ₗ[ℂ] E := LinearEquiv.ofBijective g ⟨hginj, fun z ↦ by
      obtain ⟨n, hz⟩ := hexhaustive z
      exact ⟨stage n ⟨z, hz⟩, hg_stage n ⟨z, hz⟩⟩⟩
    have hes : Continuous e.symm :=
      (locallyConvexFinal_withSeminorms stage).continuous_of_continuous_comp e.symm.toLinearMap fun p ↦
        hE.continuous_seminorm ⟨p.val.comp e.symm.toLinearMap, fun n ↦ by
          refine (p.property n).congr fun z ↦ congrArg p.val (e.injective ?_)
          change g (stage n z) = e (e.symm (z : E))
          rw [hg_stage, e.apply_symm_apply]⟩
    let eL : L ≃L[ℂ] E := ⟨e, hg, hes⟩
    exact nuclearLocallyConvex_of_equiv eL (nuclearLocallyConvex_directLimit j hNuclear inferInstance)
  let : BarrelledSpace ℂ E := ⟨fun p hp ↦ hE.continuous_seminorm ⟨p, fun n ↦ by
    let : BarrelledSpace ℂ (S n) := isFrechetTVS_barrelled (hFrechet n)
    exact (p.comp (S n).subtype).continuous_of_lowerSemicontinuous
      (hp.comp continuous_subtype_val)⟩⟩
  exact isAbsolute_of_isNuclearTVS hN hb (schauderBasis_equicontinuous_of_barrelled hb)

end
end Masullo
