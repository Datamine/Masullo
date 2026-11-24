import ElementarySchwartzCutoffs
import ElementarySchwartzTranslation
import ElementaryRadialSchwartz
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries

open Filter Function Set Topology
open scoped ContDiff NNReal

namespace Masullo

noncomputable section

section SmoothSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- Local summable majorants suffice for differentiating a smooth series.
The neighborhood and majorant may depend on the point and derivative order. -/
theorem smoothSeries_of_local_derivative_bounds {f : ι → E → ℂ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hb : ∀ (x : E) (k : ℕ), ∃ (s : Set E) (v : ι → ℝ),
      IsOpen s ∧ Convex ℝ s ∧ x ∈ s ∧ Summable v ∧
        ∀ i y, y ∈ s → ‖iteratedFDeriv ℝ k (f i) y‖ ≤ v i) :
    ContDiff ℝ ∞ (fun x ↦ ∑' i, f i x) ∧
      ∀ k x, Summable (fun i ↦ iteratedFDeriv ℝ k (f i) x) ∧
        iteratedFDeriv ℝ k (fun y ↦ ∑' i, f i y) x =
        ∑' i, iteratedFDeriv ℝ k (f i) x := by
  let F (k : ℕ) (i : ι) := iteratedFDeriv ℝ k (f i)
  have hsum (k : ℕ) (x : E) : Summable (fun i ↦ F k i x) := by
    obtain ⟨s, v, _, _, hx, hv, h⟩ := hb x k
    exact .of_norm_bounded hv (fun i ↦ h i x hx)
  have hder (k : ℕ) (x : E) :
      HasFDerivAt (fun y ↦ ∑' i, F k i y) (∑' i, fderiv ℝ (F k i) x) x := by
    obtain ⟨s, v, hs, hconv, hx, hv, h⟩ := hb x (k + 1)
    refine hasFDerivAt_tsum_of_isPreconnected hv hs hconv.isPreconnected
      (fun i y _ ↦ ?_) (fun i y hy ↦ ?_) hx (hsum k x) hx
    · exact ((hf i).differentiable_iteratedFDeriv (show (k : ℕ∞) < ∞ by exact_mod_cast ENat.natCast_lt_top k)).differentiableAt.hasFDerivAt
    · rw [show F k i = iteratedFDeriv ℝ k (f i) from rfl, norm_fderiv_iteratedFDeriv]
      exact h i y hy
  have hformula (k : ℕ) :
      iteratedFDeriv ℝ k (fun x ↦ ∑' i, f i x) = fun x ↦ ∑' i, F k i x := by
    induction k with
    | zero =>
        funext x
        simp_rw [F, iteratedFDeriv_zero_eq_comp]
        exact (continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.map_tsum
    | succ k ih =>
        funext x
        simp_rw [iteratedFDeriv_succ_eq_comp_left, ih, comp_apply]
        rw [(hder k x).fderiv]
        exact (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) => E) ℂ).symm.toContinuousLinearEquiv.map_tsum
  refine ⟨?_, fun k x ↦ ⟨hsum k x, congrFun (hformula k) x⟩⟩
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro k _
    rw [hformula]
    exact continuous_iff_continuousAt.mpr fun x ↦ (hder k x).continuousAt
  · intro k _
    rw [hformula]
    exact fun x ↦ (hder k x).differentiableAt

end SmoothSeries

section Elementary

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "S" => ElementarySchwartz m n r F

private theorem summable_integer_majorant :
    Summable (fun j : ℤ ↦ 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  have hnat : Summable (fun j : ℕ ↦ 1 / (1 + (j : ℝ)) ^ 2) := by
    simpa only [Real.rpow_two, add_comm (1 : ℝ),
      fun j : ℕ ↦ abs_of_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity)] using h
  rw [summable_int_iff_summable_nat_and_neg]
  simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
    fun j : ℕ ↦ abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using And.intro hnat hnat

private theorem shift_weight_bound (R d a : ℝ) (hd : 0 < d) (hR : 0 ≤ R)
    (ha : |a| ≤ R) (j : ℤ) :
    1 + |(j : ℝ)| ≤ (1 + (1 + R) / d) * (1 + |a + (j : ℝ) * d|) := by
  let t := |a + (j : ℝ) * d|
  have hj : |(j : ℝ)| * d ≤ t + R := by
    calc
      |(j : ℝ)| * d = |(a + (j : ℝ) * d) - a| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_pos hd]
      _ ≤ t + |a| := abs_sub _ _
      _ ≤ t + R := by linarith
  apply (mul_le_mul_iff_left₀ hd).1
  have he : (1 + (1 + R) / d) * d = d + (1 + R) := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
  rw [mul_right_comm _ (1 + t) d, he, add_mul, one_mul]
  have ht : 0 ≤ t := abs_nonneg _
  nlinarith [mul_nonneg (add_nonneg hd.le hR) ht]

private theorem exists_elementary_fibre_translation (z : A) (a : Fin r → ℤ) (b : F) :
    ∃ (v : X) (a' : Fin r → ℤ) (b' : F), ∀ x : X,
      elementaryCover x a b + z = elementaryCover (x + v) a' b' := by
  obtain ⟨w, hw⟩ := elementaryCover_surjective z.2.2.1 z.2.2.2 z.1 z.2.1
  refine ⟨(z.1, w), a + z.2.2.1, b + z.2.2.2, fun x ↦ ?_⟩
  have h : elementaryCover (z.1, w) z.2.2.1 z.2.2.2 = z := hw
  conv_lhs => rw [← h]
  exact elementaryCover_add_shift _ _ _ _ _ _

private theorem exists_elementary_translated_log_derivative_seminorm
    (l : A →+ ℝ) (hl : Continuous l) (N k : ℕ) :
    ∃ q : Seminorm ℂ S, Continuous q ∧ ∀ (f : S) (x : X) (a : Fin r → ℤ) (b : F) (z : A),
      (1 + |l (elementaryCover x a b + z)|) ^ N *
        ‖iteratedFDeriv ℝ k (fun y ↦ f (elementaryCover y a b + z)) x‖ ≤ q f := by
  obtain ⟨q, hq, hb⟩ := exists_elementary_log_derivative_seminorm l hl N k
  refine ⟨q, hq, fun f x a b z ↦ ?_⟩
  obtain ⟨v, a', b', he⟩ := exists_elementary_fibre_translation z a b
  let g (y : X) : ℂ := f (elementaryCover y a' b')
  have hf : (fun y ↦ f (elementaryCover y a b + z)) = fun y ↦ g (y + v) :=
    funext fun y ↦ congrArg f.val (he y)
  rw [hf, he x, iteratedFDeriv_comp_add_right (f := g)]
  exact hb f (x + v) a' b'

/-- On every Euclidean covering fibre of an elementary quotient, a Schwartz
orbit sum is smooth and may be differentiated term by term, for any
injectively indexed selection of translates. -/
theorem elementaryCyclicSeries_smooth {ι : Type*} (J : ι → ℤ) (hJ : Injective J)
    (l : A →+ ℝ) (hl : Continuous l) (s : A) (hs : 0 < l s)
    (f : S) (a : Fin r → ℤ) (b : F) :
    let g (i : ι) (x : X) := f (elementaryCover x a b + J i • s)
    ContDiff ℝ ∞ (fun x ↦ ∑' i, g i x) ∧
      ∀ k x, Summable (fun i ↦ iteratedFDeriv ℝ k (g i) x) ∧
        iteratedFDeriv ℝ k (fun y ↦ ∑' i, g i y) x =
        ∑' i, iteratedFDeriv ℝ k (g i) x := by
  let g (i : ι) (x : X) := f (elementaryCover x a b + J i • s)
  change ContDiff ℝ ∞ (fun x ↦ ∑' i, g i x) ∧ _
  apply smoothSeries_of_local_derivative_bounds
  · intro i
    obtain ⟨v, a', b', he⟩ := exists_elementary_fibre_translation (J i • s) a b
    have hg : g i = fun x ↦ f (elementaryCover (x + v) a' b') :=
      funext fun x ↦ congrArg f.val (he x)
    rw [hg]
    exact (f.property.1 a' b').comp (contDiff_id.add contDiff_const)
  intro x k
  obtain ⟨q, _, hq⟩ := exists_elementary_translated_log_derivative_seminorm l hl 2 k
  let p (y : X) := l (elementaryCover y a b)
  have hpEq : p = fun y : X ↦ l (elementaryCoverHom (F := F) y + elementaryCover 0 a b) := by
    funext y
    apply congrArg l
    change elementaryCover y a b = elementaryCover y 0 0 + elementaryCover 0 a b
    rw [elementaryCover_add_shift, add_zero, zero_add, zero_add]
  have hp : Continuous p := by
    rw [hpEq]
    exact hl.comp (elementaryCoverHom_continuous.add continuous_const)
  let R := |p x| + 1
  let U := {y : X | |p y| < R}
  have hU : IsOpen U := isOpen_lt hp.abs continuous_const
  have hxU : x ∈ U := by dsimp [U, R]; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  let C := 1 + (1 + R) / l s
  let M (i : ι) := (C ^ 2 * q f) * (1 / (1 + |(J i : ℝ)|) ^ 2)
  refine ⟨Metric.ball x ε, M, Metric.isOpen_ball, convex_ball x ε, Metric.mem_ball_self hε,
    (summable_integer_majorant.comp_injective hJ).mul_left _, fun i y hy ↦ ?_⟩
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpy : |p y| ≤ R := le_of_lt (hball hy)
  have hlshift : l (elementaryCover y a b + J i • s) = p y + (J i : ℝ) * l s := by
    simp only [map_add, map_zsmul, zsmul_eq_mul, p]
  have hwgt := shift_weight_bound R (l s) (p y) hs hR hpy (J i)
  have hb := hq f y a b (J i • s)
  rw [hlshift] at hb
  dsimp only [M]
  rw [mul_one_div, le_div_iff₀ (by positivity : 0 < (1 + |(J i : ℝ)|) ^ 2)]
  rw [mul_comm]
  refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hwgt _) (norm_nonneg _)).trans ?_
  rw [mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

private theorem outward_tail_sum_bound {V : Type*} [NormedAddCommGroup V]
    (D : ℕ → V) (T d B : ℝ) (hT : 0 ≤ T) (hd : 0 < d) (N : ℕ)
    (W : ℕ → ℝ) (hW : ∀ j : ℕ, T + (j : ℝ) * d ≤ W j)
    (hD : ∀ j, (1 + W j) ^ (N + 2) * ‖D j‖ ≤ B) :
    (1 + T) ^ N * ‖∑' j, D j‖ ≤
      (1 + 1 / d) ^ 2 * B * ∑' j : ℕ, 1 / (1 + (j : ℝ)) ^ 2 := by
  let w := (1 + T) ^ N
  let C := (1 + 1 / d) ^ 2 * B
  let v (j : ℕ) := 1 / (1 + (j : ℝ)) ^ 2
  have hv : Summable v := by
    apply (summable_integer_majorant.comp_injective (Nat.cast_injective (R := ℤ))).congr
    intro j
    change 1 / (1 + |((j : ℤ) : ℝ)|) ^ 2 = 1 / (1 + (j : ℝ)) ^ 2
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)]
  have hw : 1 ≤ w := one_le_pow₀ (by linarith)
  have hb (j : ℕ) : w * ‖D j‖ ≤ C * v j := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hW₀ := (add_nonneg hT (mul_nonneg hj hd.le)).trans (hW j)
    have h₂ : 1 + (j : ℝ) ≤ (1 + 1 / d) * (1 + W j) := by
      apply (mul_le_mul_iff_left₀ hd).1
      have he : (1 + 1 / d) * d = d + 1 := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
      rw [mul_right_comm _ (1 + W j) d, he, add_mul, one_mul]
      nlinarith [mul_nonneg hd.le hW₀, hW j]
    have hw' : w ≤ (1 + W j) ^ N := by
      apply pow_le_pow_left₀ (by linarith)
      linarith [mul_nonneg hj hd.le, hW j]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (j : ℝ)) h₂ 2
    dsimp only [v]
    rw [mul_one_div, le_div_iff₀ (by positivity : 0 < (1 + (j : ℝ)) ^ 2)]
    calc
      w * ‖D j‖ * (1 + (j : ℝ)) ^ 2 ≤
          (1 + W j) ^ N * ‖D j‖ * ((1 + 1 / d) * (1 + W j)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hw' (norm_nonneg _)) hpow (by positivity)
          (mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _))
      _ = (1 + 1 / d) ^ 2 * ((1 + W j) ^ (N + 2) * ‖D j‖) := by
        rw [pow_add]
        ring
      _ ≤ C := mul_le_mul_of_nonneg_left (hD j) (sq_nonneg _)
  have hA : Summable (fun j ↦ w * ‖D j‖) :=
    (hv.mul_left C).of_nonneg_of_le (fun _ ↦ mul_nonneg (zero_le_one.trans hw) (norm_nonneg _)) hb
  have hDabs : Summable (fun j ↦ ‖D j‖) :=
    hA.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ le_mul_of_one_le_left (norm_nonneg _) hw)
  calc
    w * ‖∑' j, D j‖ ≤ w * ∑' j, ‖D j‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hDabs) (zero_le_one.trans hw)
    _ = ∑' j, w * ‖D j‖ := tsum_mul_left.symm
    _ ≤ ∑' j, C * v j := hA.tsum_le_tsum hb (hv.mul_left C)
    _ = C * ∑' j, v j := tsum_mul_left

/-- With zero complete periodization, every mixed derivative of the positive
tail has arbitrarily rapid decay in the logarithmic coordinate. A single
continuous seminorm of the input controls each derivative and weight, over
all covering fibres. -/
theorem elementaryCyclicTail_log_decay (l : A →+ ℝ) (hl : Continuous l) (s : A) (hs : 0 < l s)
    (N k : ℕ) :
    ∃ q : Seminorm ℂ S, Continuous q ∧
      ∀ (f : S), (∀ z : A, (∑' j : ℤ, f (z + j • s)) = 0) →
        ∀ (x : X) (a : Fin r → ℤ) (b : F),
          (1 + |l (elementaryCover x a b)|) ^ N *
            ‖iteratedFDeriv ℝ k
              (fun y ↦ ∑' j : ℕ, f (elementaryCover y a b + (j : ℤ) • s)) x‖ ≤ q f := by
  obtain ⟨q, hq, hb⟩ := exists_elementary_translated_log_derivative_seminorm l hl (N + 2) k
  let V : ℝ := ∑' j : ℕ, 1 / (1 + (j : ℝ)) ^ 2
  let C : ℝ≥0 := ⟨(1 + 1 / l s) ^ 2 * V, mul_nonneg (sq_nonneg _) (tsum_nonneg fun _ ↦ by positivity)⟩
  refine ⟨C • q, hq.const_smul C, fun f hzero x a b ↦ ?_⟩
  let pos (j : ℕ) : ℤ := j
  let neg (j : ℕ) : ℤ := -((j : ℤ) + 1)
  have hpos : Injective pos := Nat.cast_injective
  have hneg : Injective neg := fun i j h ↦ by
    change -((i : ℤ) + 1) = -((j : ℤ) + 1) at h
    omega
  let t := l (elementaryCover x a b)
  let tail (J : ℕ → ℤ) (y : X) := ∑' j : ℕ, f (elementaryCover y a b + J j • s)
  have htail (J : ℕ → ℤ) (hJ : Injective J)
      (hside : ∀ j : ℕ, |t| + (j : ℝ) * l s ≤ |t + (J j : ℝ) * l s|) :
      (1 + |t|) ^ N * ‖iteratedFDeriv ℝ k (tail J) x‖ ≤ C.val * q f := by
    have he := (elementaryCyclicSeries_smooth J hJ l hl s hs f a b).2 k x |>.2
    change iteratedFDeriv ℝ k (tail J) x =
      ∑' j, iteratedFDeriv ℝ k (fun y ↦ f (elementaryCover y a b + J j • s)) x at he
    rw [he]
    let D (j : ℕ) := iteratedFDeriv ℝ k (fun y ↦ f (elementaryCover y a b + J j • s)) x
    have hD (j : ℕ) : (1 + |t + (J j : ℝ) * l s|) ^ (N + 2) * ‖D j‖ ≤ q f := by
      simpa only [map_add, map_zsmul, zsmul_eq_mul, t, D] using hb f x a b (J j • s)
    have H := outward_tail_sum_bound D |t| (l s) (q f) (abs_nonneg t) hs
      N (fun j ↦ |t + (J j : ℝ) * l s|) hside hD
    exact H.trans_eq (by dsimp [C, V]; ring)
  change (1 + |t|) ^ N * ‖iteratedFDeriv ℝ k (tail pos) x‖ ≤ C.val * q f
  by_cases ht : 0 ≤ t
  · apply htail pos hpos
    intro j
    have hj : 0 ≤ (j : ℝ) * l s := mul_nonneg (Nat.cast_nonneg _) hs.le
    simp [pos, abs_of_nonneg ht, abs_of_nonneg (add_nonneg ht hj)]
  · have hEq : tail pos = -tail neg := by
      funext y
      let g (j : ℤ) := f (elementaryCover y a b + j • s)
      have hp := ((elementaryCyclicSeries_smooth pos hpos l hl s hs f a b).2 0 y).1
      have hn := ((elementaryCyclicSeries_smooth neg hneg l hl s hs f a b).2 0 y).1
      let e := (continuousMultilinearCurryFin0 ℝ X ℂ).toContinuousLinearEquiv
      have hp' : Summable (fun j : ℕ ↦ g (j : ℤ)) := by
        simpa only [e, iteratedFDeriv_zero_eq_comp, comp_apply,
          ContinuousLinearEquiv.coe_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.apply_symm_apply, pos, g] using hp.mapL e.toContinuousLinearMap
      have hn' : Summable (fun j : ℕ ↦ g (-((j : ℤ) + 1))) := by
        simpa only [e, iteratedFDeriv_zero_eq_comp, comp_apply,
          ContinuousLinearEquiv.coe_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.apply_symm_apply, neg, g] using hn.mapL e.toContinuousLinearMap
      have hz := hzero (elementaryCover y a b)
      change (∑' j : ℤ, g j) = 0 at hz
      rw [tsum_of_nat_of_neg_add_one hp' hn'] at hz
      exact eq_neg_of_add_eq_zero_left hz
    rw [hEq, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
    apply htail neg hneg
    intro j
    have hj : 0 ≤ ((j : ℝ) + 1) * l s := mul_nonneg (by positivity) hs.le
    have h' : (neg j : ℝ) = -((j : ℝ) + 1) := by simp [neg]
    rw [h', abs_of_nonpos (le_of_not_ge ht)]
    rw [abs_of_nonpos (by linarith : t + -((j : ℝ) + 1) * l s ≤ 0)]
    linarith [hs.le]

/-- An exponentially damped tail of translates is Schwartz on any proper
logarithmic chart, for either orientation of the translation. -/
theorem elementaryGeometricTail_mem (l : A →+ ℝ) (hl : IsProperMap l) (s : A)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) (f : S) :
    (fun z : A ↦ ∑' j : ℕ, ((ρ ^ j : ℝ) : ℂ) • f (z + (j : ℤ) • s)) ∈
      elementarySchwartzSubmodule m n r F := by
  let g (a : Fin r → ℤ) (b : F) (j : ℕ) (x : X) :=
    ((ρ ^ j : ℝ) : ℂ) • f (elementaryCover x a b + (j : ℤ) • s)
  have hbase (a : Fin r → ℤ) (b : F) (j : ℕ) :
      ContDiff ℝ ∞ (fun x : X ↦ f (elementaryCover x a b + (j : ℤ) • s)) := by
    obtain ⟨v, a', b', he⟩ := exists_elementary_fibre_translation ((j : ℤ) • s) a b
    simp_rw [he]
    exact (f.property.1 a' b').comp (contDiff_id.add contDiff_const)
  have hg (a : Fin r → ℤ) (b : F) (j : ℕ) : ContDiff ℝ ∞ (g a b j) :=
    (hbase a b j).const_smul _
  have hnorm (a : Fin r → ℤ) (b : F) (j k : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ k (g a b j) x‖ =
        ρ ^ j * ‖iteratedFDeriv ℝ k (fun y : X ↦ f (elementaryCover y a b + (j : ℤ) • s)) x‖ := by
    let F₀ (y : X) : ℂ := f (elementaryCover y a b + (j : ℤ) • s)
    change ‖iteratedFDeriv ℝ k (((ρ ^ j : ℝ) : ℂ) • F₀) x‖ = ρ ^ j * ‖iteratedFDeriv ℝ k F₀ x‖
    have hF : ContDiff ℝ ∞ F₀ := hbase a b j
    rw [iteratedFDeriv_const_smul_apply (hF.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hρ _)]
  let C (N : ℕ) := (1 + |l s|) ^ N
  let p (N j : ℕ) := (1 + (j : ℝ)) ^ N * ρ ^ j
  have hp (N : ℕ) : Summable (p N) := by
    have hr : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hρ] using hρ'
    have H := summable_pow_mul_geometric_of_norm_lt_one N hr
    apply ((H.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h : Injective (· + 1))).div_const ρ).congr
    intro j
    change (((j + 1 : ℕ) : ℝ) ^ N * ρ ^ (j + 1)) / ρ = _
    rw [pow_succ, Nat.cast_add, Nat.cast_one, ← mul_assoc, mul_div_cancel_right₀ _ hρ.ne']
    simp [p, add_comm]
  have hb (N k : ℕ) : ∃ B : ℝ, ∀ (a : Fin r → ℤ) (b : F) (j : ℕ) (x : X),
      (1 + |l (elementaryCover x a b)|) ^ N * ‖iteratedFDeriv ℝ k (g a b j) x‖ ≤ B * p N j := by
    obtain ⟨q, _, hq⟩ := exists_elementary_translated_log_derivative_seminorm l hl.continuous N k
    refine ⟨C N * q f, fun a b j x ↦ ?_⟩
    let t := l (elementaryCover x a b)
    let v := l (elementaryCover x a b + (j : ℤ) • s)
    have hv : v = t + (j : ℝ) * l s := by
      simp only [v, t, map_add, map_zsmul, zsmul_eq_mul, Int.cast_natCast]
    have hsep : |t| ≤ |v| + (j : ℝ) * |l s| := by
      have he : t = v - (j : ℝ) * l s := by linarith
      calc
        |t| = |v - (j : ℝ) * l s| := congrArg abs he
        _ ≤ |v| + |(j : ℝ) * l s| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)]
    have hW : (1 + |t|) ^ N ≤ (1 + (j : ℝ)) ^ N * C N * (1 + |v|) ^ N := by
      rw [← mul_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hprod : 1 + (j : ℝ) * |l s| ≤ (1 + (j : ℝ)) * (1 + |l s|) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) j, abs_nonneg (l s)]
      calc
        1 + |t| ≤ (1 + (j : ℝ) * |l s|) * (1 + |v|) := by
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (abs_nonneg (l s)))
            (abs_nonneg v)]
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)
    rw [hnorm]
    change (1 + |t|) ^ N * (ρ ^ j * _) ≤ _
    rw [mul_left_comm]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
      (pow_nonneg hρ.le _)).trans ?_
    let B := ‖iteratedFDeriv ℝ k (fun y : X ↦ f (elementaryCover y a b + (j : ℤ) • s)) x‖
    calc
      _ = (C N * p N j) * ((1 + |v|) ^ N * B) := by dsimp [p, B]; ring
      _ ≤ (C N * p N j) * q f :=
        mul_le_mul_of_nonneg_left (hq f x a b ((j : ℤ) • s))
          (mul_nonneg (pow_nonneg (by positivity) _) (mul_nonneg (by positivity) (pow_nonneg hρ.le _)))
      _ = _ := by ring
  have hseries (a : Fin r → ℤ) (b : F) := by
    apply smoothSeries_of_local_derivative_bounds (hf := hg a b)
    intro x k
    obtain ⟨B, hB⟩ := hb 0 k
    refine ⟨univ, fun j ↦ B * p 0 j, isOpen_univ, convex_univ, mem_univ _, (hp 0).mul_left B,
      fun j y _ ↦ ?_⟩
    simpa only [pow_zero, one_mul] using hB a b j y
  apply elementarySchwartz_mem_of_log_derivative_bounds l hl
  · exact fun a b ↦ (hseries a b).1
  · intro N k
    obtain ⟨B, hB⟩ := hb N k
    refine ⟨∑' j, B * p N j, fun x a b ↦ ?_⟩
    let w := (1 + |l (elementaryCover x a b)|) ^ N
    let D (j : ℕ) := iteratedFDeriv ℝ k (g a b j) x
    have hw : 1 ≤ w := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
    have hA : Summable (fun j ↦ w * ‖D j‖) := ((hp N).mul_left B).of_nonneg_of_le
      (fun _ ↦ mul_nonneg (zero_le_one.trans hw) (norm_nonneg _)) (hB a b · x)
    have hDA : Summable fun j ↦ ‖D j‖ :=
      hA.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ le_mul_of_one_le_left (norm_nonneg _) hw)
    change w * ‖iteratedFDeriv ℝ k (fun y ↦ ∑' j, g a b j y) x‖ ≤ _
    rw [((hseries a b).2 k x).2]
    calc
      w * ‖∑' j, D j‖ ≤ w * ∑' j, ‖D j‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hDA) (zero_le_one.trans hw)
      _ = ∑' j, w * ‖D j‖ := tsum_mul_left.symm
      _ ≤ _ := hA.tsum_le_tsum (hB a b · x) ((hp N).mul_left B)

end Elementary

end

end Masullo
