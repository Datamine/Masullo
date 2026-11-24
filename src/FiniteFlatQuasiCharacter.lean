import FiniteLocalZeta
import FinestSubspaces
import Mathlib.Analysis.Normed.Ring.Ultra

open Filter IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- A complex number whose nonnegative powers all stay within half a unit
of one is one. -/
theorem complex_eq_one_of_powers_near_one (z : ℂ)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  let q : ℂ := ∑ i ∈ Finset.range n, z ^ i
  have hRe (i : ℕ) : (1 / 2 : ℝ) ≤ (z ^ i).re := by
    have he := (Complex.abs_re_le_norm (z ^ i - 1)).trans (h i).le
    rw [Complex.sub_re, Complex.one_re] at he
    have hl := neg_abs_le ((z ^ i).re - 1)
    linarith
  have hq : (n : ℝ) / 2 ≤ ‖q‖ := calc
    (n : ℝ) / 2 = ∑ _ ∈ Finset.range n, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ q.re := by
      change _ ≤ (∑ i ∈ Finset.range n, z ^ i).re
      rw [Complex.re_sum]
      exact Finset.sum_le_sum fun i _ ↦ hRe i
    _ ≤ ‖q‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hl := mul_le_mul_of_nonneg_right hq hpos.le
  have he : q * (z - 1) = z ^ n - 1 := geom_sum_mul z n
  rw [← norm_mul, he] at hl
  have hh := (div_lt_iff₀ hpos).mp hn
  linarith [h n]

/-- Positive-radius balls around one of radius at most one are stable under
nonnegative powers in an ultrametric normed field. -/
theorem ultrametric_norm_pow_sub_one_lt {K : Type*} [NormedField K] [IsUltrametricDist K]
    {u : K} {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hu : ‖u - 1‖ < ε) (n : ℕ) :
    ‖u ^ n - 1‖ < ε := by
  have hu₁ : ‖u‖ ≤ 1 := by
    have he := IsUltrametricDist.norm_add_le_max (u - 1) 1
    rw [sub_add_cancel, norm_one] at he
    exact he.trans (max_le (hu.le.trans hε₁) le_rfl)
  induction n with
  | zero => simpa using hε
  | succ n ih =>
    have he : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [he]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    rw [norm_mul, max_lt_iff]
    exact ⟨(mul_le_of_le_one_left (norm_nonneg _) hu₁).trans_lt ih, hu⟩

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev L := v.adicCompletion F

/-- A continuous finite-place quasi-character is locally constant.
A sufficiently small ultrametric ball about one is stable under powers,
and the target admits no nontrivial cyclic subgroup inside the chosen ball. -/
theorem finiteQuasiCharacter_isLocallyConstant (χ : (L F v)ˣ →ₜ* ℂ) :
    IsLocallyConstant (χ : (L F v)ˣ → ℂ) := by
  let U := {u : (L F v)ˣ | ‖χ u - 1‖ < 1 / 2}
  have hU : U ∈ 𝓝 (1 : (L F v)ˣ) :=
    (isOpen_lt (χ.continuous.sub continuous_const).norm continuous_const).mem_nhds
      (by simp)
  have hj : IsOpenEmbedding (Units.val : (L F v)ˣ → L F v) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
  have hN : Units.val '' U ∈ 𝓝 (1 : L F v) := by
    rw [← Units.val_one, ← hj.map_nhds_eq]
    exact Filter.image_mem_map hU
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp hN
  let ε := min r 1
  have hε : 0 < ε := lt_min hr zero_lt_one
  have hV : {u : (L F v)ˣ | ‖u.val - 1‖ < ε} ∈ 𝓝 (1 : (L F v)ˣ) :=
    (isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const).mem_nhds
      (by simpa using hε)
  have htriv : ∀ᶠ u : (L F v)ˣ in 𝓝 1, χ u = 1 := by
    filter_upwards [hV] with u hu
    apply complex_eq_one_of_powers_near_one
    intro n
    have hm : (u ^ n).val ∈ Metric.ball (1 : L F v) r := by
      rw [Metric.mem_ball, dist_eq_norm, Units.val_pow_eq_pow_val]
      exact (ultrametric_norm_pow_sub_one_lt hε (min_le_right _ _) hu n).trans_le (min_le_left _ _)
    obtain ⟨w, hw, he⟩ := hB hm
    have hwu : w = u ^ n := Units.ext he
    subst w
    change ‖χ (u ^ n) - 1‖ < 1 / 2 at hw
    simpa only [map_pow] using hw
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u
  have ht : Tendsto (fun w : (L F v)ˣ ↦ u⁻¹ * w) (𝓝 u) (𝓝 1) := by
    have hc : Continuous (fun w : (L F v)ˣ ↦ u⁻¹ * w) := continuous_const.mul continuous_id
    simpa only [inv_mul_cancel] using hc.tendsto u
  filter_upwards [ht.eventually htriv] with w hw
  calc
    χ w = χ (u * (u⁻¹ * w)) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = χ u := by
      rw [map_mul]
      have he : χ (u⁻¹ * w) = 1 := hw
      rw [he, mul_one]

private def finiteFlatMultiplier (χ : (L F v)ˣ →ₜ* ℂ) (x : L F v) : ℂ :=
  if hx : x ≠ 0 then χ (Units.mk0 x hx) else 0

@[simp] private theorem finiteFlatMultiplier_units (χ : (L F v)ˣ →ₜ* ℂ) (u : (L F v)ˣ) :
    finiteFlatMultiplier F v χ u.val = χ u := by
  rw [finiteFlatMultiplier, dite_eq_left u.ne_zero]
  exact congrArg χ (Units.ext rfl)

/-- The space of additive finite-place tests that vanish at zero. -/
def finiteFlatTests : Submodule ℂ (locallyConstantTests (L F v)) := LinearMap.ker
  ((LinearMap.proj (R := ℂ) (0 : L F v)).comp (locallyConstantTests (L F v)).subtype)

private def finiteFlatQuasiCharacterLM (χ : (L F v)ˣ →ₜ* ℂ) :
    finiteFlatTests F v →ₗ[ℂ] finiteFlatTests F v := by
  let b := finiteFlatMultiplier F v χ
  have hG (f : finiteFlatTests F v) : b * f.val.val ∈ locallyConstantTests (L F v) := by
    refine ⟨?_, f.val.property.2.mul_left⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hf := f.val.property.1
    rw [IsLocallyConstant.iff_eventually_eq] at hf
    by_cases hx : x = 0
    · subst x
      have h0 : f.val.val 0 = 0 := f.property
      filter_upwards [hf 0] with y hy
      change b y * f.val.val y = b 0 * f.val.val 0
      rw [hy, h0, mul_zero, mul_zero]
    · let u := Units.mk0 x hx
      have hj : IsOpenEmbedding (Units.val : (L F v)ˣ → L F v) :=
        IsOpenUnits.isOpenEmbedding_unitsVal
      have hb : ∀ᶠ y in 𝓝 x, b y = b x := by
        change ∀ᶠ y in 𝓝 u.val, b y = b u.val
        rw [← hj.map_nhds_eq]
        change ∀ᶠ w in 𝓝 u, b w.val = b u.val
        simp only [b, finiteFlatMultiplier_units]
        have hχ := finiteQuasiCharacter_isLocallyConstant F v χ
        rw [IsLocallyConstant.iff_eventually_eq] at hχ
        exact hχ u
      filter_upwards [hb, hf x] with y hy hz
      exact congrArg₂ (· * ·) hy hz
  refine { toFun := fun f ↦ ⟨⟨b * f.val.val, hG f⟩, ?_⟩, map_add' := ?_, map_smul' := ?_ }
  · change b 0 * f.val.val 0 = 0
    simp [b, finiteFlatMultiplier]
  · intro f g
    exact Subtype.ext (Subtype.ext (funext fun x ↦ mul_add _ _ _))
  · intro a f
    exact Subtype.ext (Subtype.ext (funext fun x ↦ mul_left_comm _ _ _))

private def finiteUnitCharacterValue (χ : (L F v)ˣ →ₜ* ℂˣ) : (L F v)ˣ →ₜ* ℂ :=
  ⟨{ toFun := fun u ↦ (χ u : ℂ), map_one' := by simp,
     map_mul' := fun a b ↦ by simp }, Units.continuous_val.comp χ.continuous⟩

private theorem finiteFlatQuasiCharacterLM_apply_units (χ : (L F v)ˣ →ₜ* ℂ)
    (f : finiteFlatTests F v) (u : (L F v)ˣ) :
    (finiteFlatQuasiCharacterLM F v χ f).val.val u.val = χ u * f.val.val u.val := by
  change finiteFlatMultiplier F v χ u.val * f.val.val u.val = _
  rw [finiteFlatMultiplier_units]

private theorem finiteFlatQuasiCharacterLM_inverse (χ : (L F v)ˣ →ₜ* ℂˣ)
    (f : finiteFlatTests F v) :
    finiteFlatQuasiCharacterLM F v (finiteUnitCharacterValue F v χ⁻¹)
      (finiteFlatQuasiCharacterLM F v (finiteUnitCharacterValue F v χ) f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  by_cases hx : x = 0
  · subst x
    exact (show _ = (0 : ℂ) from (finiteFlatQuasiCharacterLM F v _ _).property).trans
      (show f.val.val 0 = 0 from f.property).symm
  · let u := Units.mk0 x hx
    change (finiteFlatQuasiCharacterLM F v _ (finiteFlatQuasiCharacterLM F v _ f)).val.val u.val = f.val.val u.val
    rw [finiteFlatQuasiCharacterLM_apply_units, finiteFlatQuasiCharacterLM_apply_units]
    change (↑((χ u)⁻¹) : ℂ) * ((χ u : ℂ) * f.val.val u.val) = f.val.val u.val
    rw [← mul_assoc, Units.inv_mul, one_mul]

/-- Multiplication by a finite-place quasi-character, followed by zero
extension, is a continuous linear automorphism of the flat local tests. -/
def finiteFlatQuasiCharacterEquiv (χ : (L F v)ˣ →ₜ* ℂˣ) :
    letI : TopologicalSpace (locallyConstantTests (L F v)) := finestLocallyConvexTopology _
    finiteFlatTests F v ≃L[ℂ] finiteFlatTests F v := by
  letI : TopologicalSpace (locallyConstantTests (L F v)) := finestLocallyConvexTopology _
  let P := finiteFlatTests F v
  let M := finiteFlatQuasiCharacterLM F v (finiteUnitCharacterValue F v χ)
  let N := finiteFlatQuasiCharacterLM F v (finiteUnitCharacterValue F v χ⁻¹)
  let τ : TopologicalSpace P := inferInstance
  have ht : τ = finestLocallyConvexTopology P :=
    (finest_submodule_quotient P).2.2.1
  have hcontinuous (A : P →ₗ[ℂ] P) : Continuous[τ, τ] A := by
    rw [ht]
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    letI : PolynormableSpace ℂ P := (finest_withSeminorms P).toPolynormableSpace
    exact finest_linear_continuous (E := P) (F := P) A
  refine ⟨{ M with
      invFun := N
      left_inv := finiteFlatQuasiCharacterLM_inverse F v χ
      right_inv := ?_ }, hcontinuous M, hcontinuous N⟩
  intro f
  change M (N f) = f
  have h := finiteFlatQuasiCharacterLM_inverse F v χ⁻¹ f
  have he : (χ⁻¹)⁻¹ = χ := by
    apply ContinuousMonoidHom.ext
    intro u
    change ((χ u)⁻¹)⁻¹ = χ u
    exact inv_inv _
  rw [he] at h
  exact h

@[simp] theorem finiteFlatQuasiCharacterEquiv_apply_units (χ : (L F v)ˣ →ₜ* ℂˣ)
    (f : finiteFlatTests F v) (u : (L F v)ˣ) :
    letI : TopologicalSpace (locallyConstantTests (L F v)) := finestLocallyConvexTopology _
    (finiteFlatQuasiCharacterEquiv F v χ f).val.val u.val = (χ u : ℂ) * f.val.val u.val :=
  finiteFlatQuasiCharacterLM_apply_units F v (finiteUnitCharacterValue F v χ) f u

end

end Masullo
