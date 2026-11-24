import ModulatedSobolevTests
import ArchimedeanCharacters

open Filter Function Set Topology
open scoped NNReal

namespace Masullo

noncomputable section

theorem existsUnique_logComplexExponential (q : Multiplicative ℝ →ₜ* ℂ) :
    ∃! z : ℂ, ∀ x : ℝ, q (Multiplicative.ofAdd x) = Complex.exp (z * (x : ℂ)) := by
  let val (t : ℝ≥0ˣ) : ℝ := ((t : ℝ≥0) : ℝ)
  have hpos (t : ℝ≥0ˣ) : 0 < val t := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hcont : Continuous val := NNReal.continuous_coe.comp Units.continuous_val
  let j : ℝ≥0ˣ →ₜ* Multiplicative ℝ :=
    ⟨{ toFun := fun t => Multiplicative.ofAdd (Real.log (val t))
       map_one' := by change Real.log (1 : ℝ) = 0; simp
       map_mul' := fun u v => by
         change Multiplicative.ofAdd (Real.log (val u * val v)) =
           Multiplicative.ofAdd (Real.log (val u) + Real.log (val v))
         rw [Real.log_mul (hpos u).ne' (hpos v).ne'] },
      continuous_ofAdd.comp (continuous_iff_continuousAt.mpr fun t =>
        (Real.continuousAt_log (hpos t).ne').comp hcont.continuousAt)⟩
  have hp (t : ℝ≥0ˣ) (z : ℂ) : (val t : ℂ) ^ z =
      Complex.exp (z * (Real.log (val t) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos t).ne'),
      ← Complex.ofReal_log (hpos t).le, mul_comm]
  obtain ⟨z, hz, hu⟩ := existsUnique_complexPower (q.comp j)
  refine ⟨z, ?_, ?_⟩
  · intro x
    let t : ℝ≥0ˣ := Units.mk0 ⟨Real.exp x, (Real.exp_pos x).le⟩
      (fun h => (Real.exp_pos x).ne' (congrArg NNReal.toReal h))
    have hx : Real.log (val t) = x := Real.log_exp x
    have h := hz t
    change q (Multiplicative.ofAdd (Real.log (val t))) = (val t : ℂ) ^ z at h
    rw [hp, hx] at h
    exact h
  · intro w hw
    apply hu w
    intro t
    change q (Multiplicative.ofAdd (Real.log (val t))) = (val t : ℂ) ^ w
    rw [hw, hp]

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

include hτ in
/-- The logarithmic coordinates used in the group Mellin evaluation
parametrize precisely the continuous group quasi-characters. -/
theorem modulatedLogQuasiCharacter_coordinates (q : G →ₜ* ℂ) :
    ∃! p : PontryaginDual m.toMonoidHom.ker × ℂ,
      (∀ (x : ℝ) (j : m.toMonoidHom.ker),
        q (τ (Multiplicative.ofAdd x) * j.val) =
          (p.1 j : ℂ) * Complex.exp (p.2 * (x : ℂ))) ∧
      ∀ g, ‖q g‖ = Real.exp (p.2.re * Multiplicative.toAdd (m g)) := by
  let K := m.toMonoidHom.ker
  let d : K →ₜ* ℂ := ⟨q.toMonoidHom.comp K.subtype,
    q.continuous.comp continuous_subtype_val⟩
  have hnorm (u : K) : ‖d u‖ = 1 := by
    obtain ⟨v, -, hv⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := K))
      d.continuous.norm.continuousOn
    have hle (w : K) : ‖d w‖ ≤ 1 := by
      have h := hv (Set.mem_univ (w * v))
      change ‖d (w * v)‖ ≤ ‖d v‖ at h
      rw [map_mul, norm_mul] at h
      exact le_of_mul_le_mul_right (h.trans_eq (one_mul _).symm)
        (norm_pos_iff.mpr ((Group.isUnit v).map d).ne_zero)
    have hi := hle u⁻¹
    rw [map_inv, norm_inv] at hi
    exact le_antisymm (hle u) ((inv_le_one₀
      (norm_pos_iff.mpr ((Group.isUnit u).map d).ne_zero)).mp hi)
  let χ : PontryaginDual K :=
    ⟨{ toFun := fun u => ⟨d u, mem_sphere_zero_iff_norm.mpr (hnorm u)⟩
       map_one' := Circle.ext (map_one d)
       map_mul' := fun x y => Circle.ext (map_mul d x y) },
      d.continuous.subtype_mk _⟩
  obtain ⟨z, hz, hu⟩ := existsUnique_logComplexExponential (q.comp τ)
  have hcoord (x : ℝ) (j : K) :
      q (τ (Multiplicative.ofAdd x) * j.val) = (χ j : ℂ) * Complex.exp (z * (x : ℂ)) := by
    rw [map_mul, mul_comm]
    exact congrArg (d j * ·) (hz x)
  refine ⟨(χ, z), ⟨hcoord, ?_⟩, ?_⟩
  · intro g
    let j : K := ⟨g / τ (m g), by
      change m (g / τ (m g)) = 1
      rw [map_div, hτ, div_self']⟩
    have hj : τ (m g) * j.val = g := by
      change τ (m g) * (g / τ (m g)) = g
      rw [← mul_div_assoc, mul_div_cancel_left]
    have h := hcoord (Multiplicative.toAdd (m g)) j
    change q (τ (m g) * j.val) = _ at h
    rw [hj] at h
    rw [h, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp, Complex.mul_re]
    simp
  · rintro ⟨η, w⟩ ⟨he, _⟩
    apply Prod.ext
    · apply DFunLike.ext
      intro j
      apply Circle.ext
      simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using
        (he 0 j).symm.trans (hcoord 0 j)
    · apply hu w
      intro x
      have h := he x (1 : K)
      change q (τ (Multiplicative.ofAdd x)) = _
      simpa only [Subgroup.coe_one, mul_one, map_one, Circle.coe_one, one_mul] using h

include hτ in
omit [CompactSpace m.toMonoidHom.ker] in
/-- Each kernel character and exponent determines an actual continuous
quasi-character in the logarithmic coordinates. -/
theorem modulatedLogQuasiCharacter_of_coordinates [IsTopologicalGroup G]
    (χ : PontryaginDual m.toMonoidHom.ker) (z : ℂ) :
    ∃ q : G →ₜ* ℂ, ∀ (x : ℝ) (j : m.toMonoidHom.ker),
      q (τ (Multiplicative.ofAdd x) * j.val) = (χ j : ℂ) * Complex.exp (z * (x : ℂ)) := by
  let K := m.toMonoidHom.ker
  have hK (g : G) : g / τ (m g) ∈ K := by
    change m (g / τ (m g)) = 1
    rw [map_div, hτ, div_self']
  let P (g : G) : K := ⟨g / τ (m g), hK g⟩
  have hP : Continuous P :=
    (continuous_id.div' (τ.continuous.comp m.continuous)).subtype_mk hK
  have hmul (g h : G) : P (g * h) = P g * P h := by
    apply Subtype.ext
    change (g * h) / τ (m (g * h)) = (g / τ (m g)) * (h / τ (m h))
    rw [map_mul, map_mul, mul_div_mul_comm]
  have hone : P 1 = 1 := by
    apply Subtype.ext
    change 1 / τ (m 1) = 1
    simp
  let A (g : G) := Multiplicative.toAdd (m g)
  have hA : Continuous A := continuous_toAdd.comp m.continuous
  have hA_mul (g h : G) : A (g * h) = A g + A h := by
    change Multiplicative.toAdd (m (g * h)) = _
    rw [map_mul]; rfl
  let q : G →ₜ* ℂ :=
    ⟨{ toFun := fun g => (χ (P g) : ℂ) * Complex.exp (z * (A g : ℂ))
       map_one' := by
         simp only [hone, map_one, Circle.coe_one, one_mul]
         have h : A 1 = 0 := by change Multiplicative.toAdd (m 1) = 0; rw [map_one]; rfl
         rw [h, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
       map_mul' := by
         intro g h
         rw [hmul, hA_mul, map_mul, Circle.coe_mul, Complex.ofReal_add, mul_add, Complex.exp_add]
         ac_rfl },
       ((continuous_subtype_val.comp χ.continuous).comp hP).mul
         (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hA)))⟩
  refine ⟨q, fun x j => ?_⟩
  have hm : m (τ (Multiplicative.ofAdd x) * j.val) = Multiplicative.ofAdd x := by
    rw [map_mul, hτ, show m j.val = 1 from j.property, mul_one]
  have hp : P (τ (Multiplicative.ofAdd x) * j.val) = j := by
    apply Subtype.ext
    change (τ (Multiplicative.ofAdd x) * j.val) / τ (m (τ (Multiplicative.ofAdd x) * j.val)) = _
    rw [hm, mul_div_cancel_left]
  change (χ (P (τ (Multiplicative.ofAdd x) * j.val)) : ℂ) *
    Complex.exp (z * (Multiplicative.toAdd (m (τ (Multiplicative.ofAdd x) * j.val)) : ℝ)) = _
  rw [hm, hp]
  rfl

end

end Masullo
