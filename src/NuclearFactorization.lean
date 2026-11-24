import LocallyConvexNuclearTrace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Convex.Gauge

open Bornology Filter Function Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

universe u v w

section Coordinates

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

private abbrev Coordinates := lp (fun _ : ℕ => ℂ) ∞

omit [IsTopologicalAddGroup E] in
private theorem dualFamily_pointwise_bounded (φ : ℕ → E →L[ℂ] ℂ)
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) (x : E) :
    BddAbove (range fun n => ‖φ n x‖) := by
  have hc : Tendsto (fun c : ℂ => c • x) (𝓝 0) (𝓝 0) := by
    have ht : Continuous (fun c : ℂ => c • x) := continuous_id.smul continuous_const
    simpa only [zero_smul] using ht.tendsto 0
  have h := hc.eventually (NuclearExpansion.eventually_norm_le hφ zero_lt_one)
  obtain ⟨r, hr, hco⟩ := Metric.eventually_nhds_iff.mp h
  let c : ℂ := ↑(r/2 : ℝ)
  have hc_norm : ‖c‖ = r/2 := by
    rw [show ‖c‖ = ‖(↑(r/2 : ℝ) : ℂ)‖ from rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
  have hrc : dist c 0 < r := by rw [dist_zero_right, hc_norm]; exact half_lt_self hr
  refine ⟨(r/2)⁻¹, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hh := hco hrc n
  rw [map_smul, smul_eq_mul, norm_mul, hc_norm] at hh
  simpa only [mul_one] using (le_inv_mul_iff₀ (half_pos hr)).mpr hh

/-- An equicontinuous family is the coordinate family of a continuous
linear map into the Banach space of bounded sequences. -/
private def dualFamilyCoordinates (φ : ℕ → E →L[ℂ] ℂ)
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) : E →L[ℂ] Coordinates := by
  let L : E →ₗ[ℂ] Coordinates :=
    { toFun := fun x => ⟨fun n => φ n x, memℓp_infty_iff.mpr (dualFamily_pointwise_bounded φ hφ x)⟩
      map_add' := fun x y => Subtype.ext (funext fun n => (φ n).map_add x y)
      map_smul' := fun c x => Subtype.ext (funext fun n => (φ n).map_smul c x) }
  refine ⟨L, continuous_of_continuousAt_zero L ?_⟩
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [NuclearExpansion.eventually_norm_le hφ (half_pos hε)] with x hx
  rw [dist_zero_right]
  exact (lp.norm_le_of_forall_le (half_pos hε).le hx).trans_lt (half_lt_self hε)

private def denseCoordinates (φ : ℕ → E →L[ℂ] ℂ)
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) :
    E →L[ℂ] (LinearMap.range (dualFamilyCoordinates φ hφ).toLinearMap).topologicalClosure :=
  (dualFamilyCoordinates φ hφ).codRestrict _ (fun x => subset_closure (mem_range_self x))

private theorem denseCoordinates_dense (φ : ℕ → E →L[ℂ] ℂ)
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) : DenseRange (denseCoordinates φ hφ) := by
  intro x
  rw [closure_subtype, ← range_comp]
  exact x.property

private def coordinatesFunctional (φ : ℕ → E →L[ℂ] ℂ)
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) (n : ℕ) :
    (LinearMap.range (dualFamilyCoordinates φ hφ).toLinearMap).topologicalClosure →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) ∞ n).comp (Submodule.subtypeL _)

private theorem coordinatesFunctional_norm_le (φ : ℕ → E →L[ℂ] ℂ)
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) (n : ℕ) :
    ‖coordinatesFunctional φ hφ n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.val n‖ ≤ 1 * ‖x.val‖
  rw [one_mul]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero x.val n

end Coordinates

section Banach

variable {H : Type w} {B : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]
variable [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- The Banach-space form of a nuclear presentation. The series here
converges in operator norm. -/
structure BanachNuclearExpansion (N : H →L[ℂ] B) where
  coeff : ℕ → ℂ
  functional : ℕ → H →L[ℂ] ℂ
  vector : ℕ → B
  coeff_summable : Summable (fun n => ‖coeff n‖)
  functional_bound : ∀ n, ‖functional n‖ ≤ 1
  vector_bound : ∀ n, ‖vector n‖ ≤ 1
  hasSum : HasSum (fun n => coeff n • (functional n).smulRight (vector n)) N

namespace BanachNuclearExpansion

/-- A rank-one family with summable products of factor norms yields a
normalized Banach nuclear expansion. Only nonzero terms need enumeration. -/
theorem nonempty_of_rankOne_hasSum {ι : Type*} {N : H →L[ℂ] B}
    (f : ι → H →L[ℂ] ℂ) (w : ι → B) (hn : Summable (fun i => ‖f i‖ * ‖w i‖))
    (hs : HasSum (fun i => (f i).smulRight (w i)) N) :
    Nonempty (BanachNuclearExpansion N) := by
  classical
  let I := Function.support (fun i => ‖f i‖ * ‖w i‖)
  have hc : I.Countable := hn.countable_support
  letI : Countable I := hc.to_subtype
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  let F : ℕ → H →L[ℂ] ℂ := Function.extend e (f ∘ Subtype.val) 0
  let W : ℕ → B := Function.extend e (w ∘ Subtype.val) 0
  have hF (i : I) : F (e i) = f i := he.extend_apply _ _ _
  have hW (i : I) : W (e i) = w i := he.extend_apply _ _ _
  have hF0 (n : ℕ) (hn' : n ∉ range e) : F n = 0 :=
    Function.extend_apply' _ _ _ (by simpa only [Set.mem_range, not_exists] using hn')
  have hm (j : ι) (hj : j ∉ range (Subtype.val : I → ι)) : ‖f j‖ * ‖w j‖ = 0 := by
    by_contra hh
    exact hj ⟨⟨j, hh⟩, rfl⟩
  have hz (j : ι) (hj : j ∉ range (Subtype.val : I → ι)) :
      (f j).smulRight (w j) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    exact ((f j).norm_smulRight_apply (w j)).le.trans_eq (hm j hj)
  have hnorm : Summable (fun n => ‖F n‖ * ‖W n‖) := by
    have hI := (Subtype.val_injective.hasSum_iff hm).mpr hn.hasSum
    have hN : HasSum (fun n => ‖F n‖ * ‖W n‖) (∑' i, ‖f i‖ * ‖w i‖) := by
      refine (he.hasSum_iff (fun n h => by simp [hF0 n h])).mp ?_
      change HasSum (fun i : I => ‖F (e i)‖ * ‖W (e i)‖) _
      change HasSum (fun i : I => ‖f i‖ * ‖w i‖) _ at hI
      simpa only [hF, hW] using hI
    exact hN.summable
  have hop : HasSum (fun n => (F n).smulRight (W n)) N := by
    have hI := (Subtype.val_injective.hasSum_iff hz).mpr hs
    refine (he.hasSum_iff (fun n h => by simp [hF0 n h])).mp ?_
    change HasSum (fun i : I => (F (e i)).smulRight (W (e i))) N
    change HasSum (fun i : I => (f i).smulRight (w i)) N at hI
    simpa only [hF, hW] using hI
  let a (n : ℕ) := (‖F n‖ : ℂ)
  let b (n : ℕ) := (‖W n‖ : ℂ)
  have ha (n : ℕ) : ‖a n‖ = ‖F n‖ := Complex.norm_of_nonneg (norm_nonneg _)
  have hb (n : ℕ) : ‖b n‖ = ‖W n‖ := Complex.norm_of_nonneg (norm_nonneg _)
  refine ⟨⟨fun n => a n * b n, fun n => (a n)⁻¹ • F n, fun n => (b n)⁻¹ • W n,
    ?_, ?_, ?_, ?_⟩⟩
  · simpa only [norm_mul, ha, hb] using hnorm
  · intro n
    rw [norm_smul, norm_inv, ha]
    by_cases h : ‖F n‖ = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  · intro n
    rw [norm_smul, norm_inv, hb]
    by_cases h : ‖W n‖ = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  · suffices heq : ∀ n : ℕ,
        (a n * b n) • ((a n)⁻¹ • F n).smulRight ((b n)⁻¹ • W n) =
          (F n).smulRight (W n) by simpa only [heq] using hop
    intro n
    by_cases hf : F n = 0
    · simp [a, hf]
    by_cases hw : W n = 0
    · simp [b, hw]
    have ha0 : a n ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf)
    have hb0 : b n ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
    ext x
    simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, smul_smul]
    congr 1
    field_simp

private theorem rankOne_summable [CompleteSpace B] (c : ℕ → ℂ) (φ : ℕ → H →L[ℂ] ℂ)
    (v : ℕ → B) (hc : Summable (fun n => ‖c n‖))
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (hv : ∀ n, ‖v n‖ ≤ 1) :
    Summable (fun n => c n • (φ n).smulRight (v n)) := by
  refine hc.of_norm_bounded fun n => ?_
  have hn : ‖(φ n).smulRight (v n)‖ ≤ 1 := by
    calc
      _ ≤ ‖φ n‖ * ‖v n‖ := ((φ n).norm_smulRight_apply (v n)).le
      _ ≤ 1 := by simpa using mul_le_mul (hφ n) (hv n) (norm_nonneg _) zero_le_one
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _)

theorem hasSum_apply {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) (x : H) :
    HasSum (fun n => (R.coeff n * R.functional n x) • R.vector n) (N x) := by
  have h := (ContinuousLinearMap.apply ℂ B x).hasSum R.hasSum
  change HasSum (fun n => ((R.coeff n) • (R.functional n).smulRight (R.vector n)) x) (N x) at h
  simpa only [smul_apply, ContinuousLinearMap.smulRight_apply, mul_smul] using h

/-- The normalized Banach presentation agrees with the pointwise
null-sequence series in (C.2.4.2). -/
theorem nonempty_iff_null_series [CompleteSpace B] {N : H →L[ℂ] B} :
    Nonempty (BanachNuclearExpansion N) ↔
      ∃ (c : ℕ → ℂ) (f : ℕ → H →L[ℂ] ℂ) (w : ℕ → B),
        Summable (fun n => ‖c n‖) ∧ Tendsto f atTop (𝓝 0) ∧ Tendsto w atTop (𝓝 0) ∧
          ∀ x, HasSum (fun n => (c n * f n x) • w n) (N x) := by
  constructor
  · rintro ⟨R⟩
    obtain ⟨s, hs, hs0, hsum⟩ :=
      summable_div_positive_null _ R.coeff_summable (fun _ => norm_nonneg _)
    let d (n : ℕ) : ℂ := (Real.sqrt (s n) : ℂ)
    have hd (n : ℕ) : ‖d n‖ = Real.sqrt (s n) := Complex.norm_of_nonneg (Real.sqrt_nonneg _)
    have hd0 : Tendsto (fun n => Real.sqrt (s n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hs0
    refine ⟨fun n => R.coeff n / (s n : ℂ), fun n => d n • R.functional n,
      fun n => d n • R.vector n, ?_, ?_, ?_, ?_⟩
    · simpa only [norm_div, Complex.norm_real, Real.norm_of_nonneg (hs _).le] using hsum
    · apply tendsto_zero_iff_norm_tendsto_zero.mpr
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hd0
      rw [norm_smul, hd]
      exact (mul_le_mul_of_nonneg_left (R.functional_bound n) (Real.sqrt_nonneg _)).trans_eq
        (mul_one _)
    · apply tendsto_zero_iff_norm_tendsto_zero.mpr
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hd0
      rw [norm_smul, hd]
      exact (mul_le_mul_of_nonneg_left (R.vector_bound n) (Real.sqrt_nonneg _)).trans_eq (mul_one _)
    · intro x
      have hterm (n : ℕ) :
          ((R.coeff n / (s n : ℂ)) * (d n • R.functional n) x) • (d n • R.vector n) =
            (R.coeff n * R.functional n x) • R.vector n := by
        rw [smul_apply, smul_eq_mul, smul_smul]
        congr 1
        have hd2 : d n ^ 2 = (s n : ℂ) := by
          dsimp [d]
          exact_mod_cast Real.sq_sqrt (hs n).le
        field_simp [Complex.ofReal_ne_zero.mpr (hs n).ne']
        calc
          _ = (R.coeff n * R.functional n x) * d n ^ 2 := by ring
          _ = _ := by rw [hd2]; ring
      simpa only [hterm] using R.hasSum_apply x
  · rintro ⟨c, f, w, hc, hf, hw, hs⟩
    obtain ⟨A, hA⟩ := (tendsto_zero_iff_norm_tendsto_zero.mp hf).bddAbove_range
    obtain ⟨D, hD⟩ := (tendsto_zero_iff_norm_tendsto_zero.mp hw).bddAbove_range
    have hAn : 0 ≤ A := (norm_nonneg (f 0)).trans (hA (mem_range_self 0))
    have hDn : 0 ≤ D := (norm_nonneg (w 0)).trans (hD (mem_range_self 0))
    let g (n : ℕ) := c n • f n
    have hmass : Summable (fun n => ‖g n‖ * ‖w n‖) := by
      refine (hc.mul_right (A * D)).of_nonneg_of_le
        (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun n => ?_
      change ‖c n • f n‖ * ‖w n‖ ≤ ‖c n‖ * (A * D)
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hA (mem_range_self n)) (hD (mem_range_self n)) (norm_nonneg _) hAn)
        (norm_nonneg _)
    have hop : Summable (fun n => (g n).smulRight (w n)) :=
      hmass.of_norm_bounded fun n => ((g n).norm_smulRight_apply (w n)).le
    have hN : (∑' n, (g n).smulRight (w n)) = N := by
      ext x
      apply ((ContinuousLinearMap.apply ℂ B x).hasSum hop.hasSum).unique
      change HasSum (fun n => (g n).smulRight (w n) x) (N x)
      simpa only [g, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul] using hs x
    exact nonempty_of_rankOne_hasSum g w hmass (hN ▸ hop.hasSum)

def scale {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) (c : ℂ) :
    BanachNuclearExpansion (c • N) where
  coeff n := c * R.coeff n
  functional := R.functional
  vector := R.vector
  coeff_summable := by simpa only [norm_mul] using R.coeff_summable.mul_left ‖c‖
  functional_bound := R.functional_bound
  vector_bound := R.vector_bound
  hasSum := by simpa only [mul_smul] using R.hasSum.const_smul c

def partialSum {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) (k : ℕ) : H →L[ℂ] B :=
  ∑ n ∈ Finset.range k, R.coeff n • (R.functional n).smulRight (R.vector n)

theorem partialSum_tendsto {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) :
    Tendsto R.partialSum atTop (𝓝 N) :=
  R.hasSum.tendsto_sum_nat

/-- A Banach nuclear map is compact. -/
theorem isCompactOperator [CompleteSpace B] {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) :
    IsCompactOperator N := by
  apply isCompactOperator_of_tendsto R.partialSum_tendsto
  apply Eventually.of_forall
  intro k
  unfold partialSum
  have hTerm (n : ℕ) : IsCompactOperator (R.coeff n • (R.functional n).smulRight (R.vector n) : H →L[ℂ] B) := by
    have h := (isCompactOperator_of_locallyCompactSpace_dom (R.functional n)).clm_comp
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (R.vector n))
    exact h.smul (R.coeff n)
  have hsum (S : Finset ℕ) :
      IsCompactOperator ((∑ n ∈ S, R.coeff n • (R.functional n).smulRight (R.vector n)) : H →L[ℂ] B) := by
    classical
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      change IsCompactOperator (fun _ : H => (0 : B))
      exact isCompactOperator_zero
    | insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact (hTerm j).add ih
  exact hsum _

end BanachNuclearExpansion

end Banach

section Factorization

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [T2Space F]
variable {B : Type w} [NormedAddCommGroup B] [NormedSpace ℂ B]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- A presentation through a complete disk gives a Banach nuclear
factorization through the completion of its coordinate norm. -/
theorem NuclearExpansion.exists_banach_factorization [CompleteSpace B]
    {J : B →L[ℂ] F} {A : E →L[ℂ] F} (R : NuclearExpansion J A) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : NormedSpace ℂ H) (_ : CompleteSpace H)
      (i : E →L[ℂ] H) (N : H →L[ℂ] B),
      DenseRange i ∧ A = J.comp (N.comp i) ∧ ∃ S : BanachNuclearExpansion N,
        S.coeff = R.coeff ∧ S.vector = R.vector ∧ ∀ n x, S.functional n (i x) = R.functional n x := by
  let P := LinearMap.range (dualFamilyCoordinates R.functional R.equicont).toLinearMap
  let H := P.topologicalClosure
  letI : CompleteSpace H := P.isClosed_topologicalClosure.completeSpace_coe
  let i := denseCoordinates R.functional R.equicont
  let φ := coordinatesFunctional R.functional R.equicont
  have hφ := coordinatesFunctional_norm_le R.functional R.equicont
  let f (n : ℕ) := R.coeff n • (φ n).smulRight (R.vector n)
  have hf : Summable f :=
    BanachNuclearExpansion.rankOne_summable _ _ _ R.coeff_summable hφ R.vector_bound
  let N := ∑' n, f n
  let S : BanachNuclearExpansion N :=
    ⟨R.coeff, φ, R.vector, R.coeff_summable, hφ, R.vector_bound, hf.hasSum⟩
  refine ⟨H, inferInstance, inferInstance, inferInstance, i, N,
    denseCoordinates_dense R.functional R.equicont, ?_, ⟨S, rfl, rfl, fun _ _ => rfl⟩⟩
  ext x
  apply (R.hasSum_apply x).unique
  have h := J.hasSum (S.hasSum_apply (i x))
  change HasSum (fun n => J ((R.coeff n * R.functional n x) • R.vector n)) (J (N (i x))) at h
  simpa only [ContinuousLinearMap.comp_apply, map_smul] using h

/-- An operator-norm nuclear series on a Banach core gives the
equicontinuous expansion on the original space. -/
def BanachNuclearExpansion.toNuclearExpansion {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) (i : E →L[ℂ] H) (J : B →L[ℂ] F) :
    NuclearExpansion J (J.comp (N.comp i)) where
  coeff := R.coeff
  functional n := (R.functional n).comp i
  vector := R.vector
  coeff_summable := R.coeff_summable
  equicont := by
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have ev : ∀ᶠ x in 𝓝 0, ‖i x‖ < ε := by
      have ht := i.continuous.tendsto 0
      rw [map_zero] at ht
      simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp ht ε hε)
    filter_upwards [ev] with x hx n
    simp only [ContinuousLinearMap.comp_apply, map_zero, dist_zero_left]
    exact ((R.functional n).le_opNorm (i x)).trans_lt
      ((mul_le_mul_of_nonneg_right (R.functional_bound n) (norm_nonneg _)).trans_lt (by simpa using hx))
  vector_bound := R.vector_bound
  hasSum_apply x := by
    simpa only [ContinuousLinearMap.comp_apply, map_smul] using (J.hasSum (R.hasSum_apply (i x)))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [T2Space F] in
/-- The series converges uniformly on any von Neumann bounded subset of
the original domain, in the target's own topology. -/
theorem BanachNuclearExpansion.uniform_on_bounded {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {N : H →L[ℂ] B} (R : BanachNuclearExpansion N) (i : E →L[ℂ] H) (J : B →L[ℂ] F)
    {D : Set E} (hD : IsVonNBounded ℂ D) {V : Set F} (hV : V ∈ 𝓝 0) :
    ∀ᶠ k in atTop, ∀ x ∈ D, J ((R.partialSum k) (i x)) - J (N (i x)) ∈ V := by
  obtain ⟨M, hM⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hD.image i)
  have hJ : Tendsto J (𝓝 0) (𝓝 0) := by simpa only [map_zero] using J.continuous.tendsto 0
  obtain ⟨δ, hδ, hJδ⟩ := Metric.eventually_nhds_iff.mp (hJ.eventually hV)
  have hC : 0 < 1 + |M| := by positivity
  have he := (Metric.tendsto_nhds.mp R.partialSum_tendsto) (δ / (1 + |M|)) (div_pos hδ hC)
  filter_upwards [he] with k hk x hx
  rw [dist_eq_norm] at hk
  rw [← map_sub]
  apply hJδ
  rw [dist_zero_right]
  change ‖(R.partialSum k - N) (i x)‖ < δ
  calc
    _ ≤ ‖R.partialSum k - N‖ * ‖i x‖ := (R.partialSum k - N).le_opNorm (i x)
    _ ≤ ‖R.partialSum k - N‖ * (1 + |M|) :=
      mul_le_mul_of_nonneg_left ((hM (i x) ⟨x, hx, rfl⟩).trans (by linarith [le_abs_self M])) (norm_nonneg _)
    _ < δ := (lt_div_iff₀ hC).mp hk


omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem NuclearExpansion.uniform_on_bounded [CompleteSpace B]
    {J : B →L[ℂ] F} {A : E →L[ℂ] F} (R : NuclearExpansion J A)
    {D : Set E} (hD : IsVonNBounded ℂ D) {V : Set F} (hV : V ∈ 𝓝 0) :
    ∀ᶠ k in atTop, ∀ x ∈ D,
      (∑ n ∈ Finset.range k, (R.coeff n * R.functional n x) • J (R.vector n)) - A x ∈ V := by
  obtain ⟨H, _, _, _, i, N, _, rfl, S, hcoeff, hvec, hfun⟩ := R.exists_banach_factorization
  filter_upwards [S.uniform_on_bounded i J hD hV] with k hk x hx
  have h := hk x hx
  have he (n : ℕ) :
      ((S.coeff n • (S.functional n).smulRight (S.vector n)) : H →L[ℂ] B) (i x) =
        (R.coeff n * R.functional n x) • R.vector n := by
    rw [smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul, hcoeff, hvec, hfun]
  have hs := map_sum (ContinuousLinearMap.apply ℂ B (i x))
    (fun n => S.coeff n • (S.functional n).smulRight (S.vector n)) (Finset.range k)
  change (S.partialSum k) (i x) =
    ∑ n ∈ Finset.range k, (S.coeff n • (S.functional n).smulRight (S.vector n)) (i x) at hs
  simp only [he] at hs
  rw [hs, map_sum] at h
  simp only [map_smul] at h
  exact h

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- A nuclear expansion through a complete disk maps some identity
neighborhood into a relatively compact subset of the target. -/
theorem NuclearExpansion.locally_compact_image [CompleteSpace B]
    {J : B →L[ℂ] F} {A : E →L[ℂ] F} (R : NuclearExpansion J A) :
    ∃ U ∈ 𝓝 (0 : E), IsCompact (closure (A '' U)) := by
  obtain ⟨H, _, _, _, i, N, _, rfl, S, _, _, _⟩ := R.exists_banach_factorization
  have h : IsCompactOperator (J.comp (N.comp i)) :=
    (S.isCompactOperator.comp_clm i).clm_comp J
  exact (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mp h

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- A Banach factorization can be normalized to carry the unit ball of
the source Banach core into the unit ball of the target disk. -/
theorem BanachNuclearExpansion.normalized_source {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] {N : H →L[ℂ] B}
    (S : BanachNuclearExpansion N) (i : E →L[ℂ] H) (hi : DenseRange i) :
    ∃ (i' : E →L[ℂ] H) (N' : H →L[ℂ] B),
      DenseRange i' ∧ ‖N'‖ ≤ 1 ∧ N'.comp i' = N.comp i ∧ Nonempty (BanachNuclearExpansion N') := by
  let d : ℝ := 1 + ‖N‖
  have hd : 0 < d := by positivity
  let c : ℂ := ↑d
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  refine ⟨c • i, c⁻¹ • N, ?_, ?_, ?_, ⟨S.scale c⁻¹⟩⟩
  · have eq : range (c • i) = range i := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨c • x, i.map_smul c x⟩
      · rintro ⟨x, rfl⟩
        exact ⟨c⁻¹ • x, by simp [smul_apply, map_smul, smul_smul, hc]⟩
    exact denseRange_iff_closure_range.mpr (eq ▸ denseRange_iff_closure_range.mp hi)
  · rw [norm_smul, norm_inv]
    have eq : ‖c‖ = d := by dsimp [c]; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    rw [eq]
    apply (inv_mul_le_iff₀ hd).mpr
    simp [d]
  · ext x
    simp [ContinuousLinearMap.comp_apply, smul_smul, hc]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [T2Space F] in
theorem banach_unit_preimage_mapsTo_disk {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (i : E →L[ℂ] H) (N : H →L[ℂ] B) (J : B →L[ℂ] F) (hN : ‖N‖ ≤ 1) :
    MapsTo (J.comp (N.comp i)) (i ⁻¹' Metric.closedBall 0 1) (J '' Metric.closedBall 0 1) := by
  intro x hx
  refine ⟨N (i x), ?_, rfl⟩
  change i x ∈ Metric.closedBall 0 1 at hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact (N.le_opNorm (i x)).trans (by simpa using mul_le_mul hN hx (norm_nonneg _) zero_le_one)

section Gauge

variable [Module ℝ E] [IsScalarTower ℝ ℂ E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- The norm of the Banach core agrees with the Minkowski functional of
the inverse image of its closed unit ball. -/
theorem banach_core_gauge (i : E →L[ℂ] H) (x : E) :
    gauge (i ⁻¹' Metric.closedBall 0 1) x = ‖i x‖ := by
  have eq : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ i ⁻¹' Metric.closedBall 0 1} =
      {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • i x ∈ Metric.closedBall 0 1} := by
    ext r
    change (r ∈ Ioi 0 ∧ i (r⁻¹ • x) ∈ Metric.closedBall 0 1) ↔ _
    rw [show i (r⁻¹ • x) = r⁻¹ • i x from (i.restrictScalars ℝ).map_smul _ _]
    rfl
  calc
    _ = gauge (Metric.closedBall 0 1) (i x) := by rw [gauge_def', gauge_def', eq]
    _ = _ := by simp only [gauge_closedBall zero_le_one, div_one]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- The preimage of the unit ball is a convex circled zero neighborhood,
and the core is isometric for the seminorm given by its gauge. -/
theorem banach_core_neighborhood (i : E →L[ℂ] H) :
    let U := i ⁻¹' Metric.closedBall 0 1
    U ∈ 𝓝 (0 : E) ∧ Convex ℝ U ∧ Balanced ℂ U ∧
      (∀ x : E, gauge U x = ‖i x‖) := by
  intro U
  have h : Tendsto i (𝓝 0) (𝓝 0) := by simpa only [map_zero] using i.continuous.tendsto 0
  refine ⟨h (Metric.closedBall_mem_nhds 0 zero_lt_one),
    (convex_closedBall 0 1).linear_preimage (i.restrictScalars ℝ).toLinearMap, ?_, banach_core_gauge i⟩
  intro c hc y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change i (c • x) ∈ Metric.closedBall 0 1
  rw [map_smul]
  exact balanced_closedBall_zero c hc (smul_mem_smul_set hx)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- Characterization of nuclear operators by a norm-convergent Banach-core
factorization through the prescribed complete disk. The dense core is the
separated completion for the gauge of the constructed convex circled neighborhood. -/
theorem nuclearExpansion_iff_banachCore [CompleteSpace B]
    (J : B →L[ℂ] F) (hJ : Injective J) (A : E →L[ℂ] F) :
    Nonempty (NuclearExpansion J A) ↔
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : NormedSpace ℂ H) (_ : CompleteSpace H)
        (i : E →L[ℂ] H) (N : H →L[ℂ] B) (U : Set E),
        DenseRange i ∧ Convex ℝ U ∧ Balanced ℂ U ∧ U ∈ 𝓝 (0 : E) ∧
        (∀ x : E, gauge U x = ‖i x‖) ∧ MapsTo A U (J '' Metric.closedBall 0 1) ∧
        IsVonNBounded ℂ (J '' Metric.closedBall 0 1) ∧
        Injective J ∧ Nonempty (BanachNuclearExpansion N) ∧ A = J.comp (N.comp i) := by
  constructor
  · rintro ⟨R⟩
    obtain ⟨H, _, _, _, i, N, hi, he, S, _, _, _⟩ := R.exists_banach_factorization
    obtain ⟨i', N', hi', hN', he', hS'⟩ := S.normalized_source i hi
    obtain ⟨hU, hconv, hbal, hgauge⟩ := banach_core_neighborhood i'
    have hiB : IsVonNBounded ℂ (J '' Metric.closedBall 0 1) :=
      (NormedSpace.isVonNBounded_closedBall ℂ B 1).image J
    have hA : A = J.comp (N'.comp i') := he.trans (congrArg J.comp he'.symm)
    exact ⟨H, inferInstance, inferInstance, inferInstance, i', N', _, hi',
      hconv, hbal, hU, hgauge, hA.symm ▸ banach_unit_preimage_mapsTo_disk i' N' J hN',
      hiB, hJ, hS', hA⟩
  · rintro ⟨H, _, _, _, i, N, U, _, _, _, _, _, _, _, _, ⟨S⟩, rfl⟩
    exact ⟨S.toNuclearExpansion i J⟩


end Gauge

end Factorization

end

end Masullo
