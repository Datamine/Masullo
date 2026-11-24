import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Filter Function Set Topology

namespace Masullo

noncomputable section

/-- The half-open sector of width one (n)-th of a turn. -/
def circleSector (n : ℕ) : Set Circle := Circle.exp '' Ico 0 (2 * Real.pi / n)

private theorem sectorWidth_pos {n : ℕ} (hn : n ≠ 0) :
    0 < 2 * Real.pi / (n : ℝ) :=
  div_pos Real.two_pi_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))

private theorem sectorWidth_mul {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * (2 * Real.pi / (n : ℝ)) = 2 * Real.pi := by
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]

/-- Each phase has a unique rotation by an (n)-th root of unity into
the half-open sector. -/
theorem circleSector_unique_rotation (n : ℕ) [NeZero n] (z : Circle) :
    ∃! r : rootsOfUnity n Circle, (r.val : Circle) * z ∈ circleSector n := by
  let d := 2 * Real.pi / (n : ℝ)
  have hd : 0 < d := sectorWidth_pos (NeZero.ne n)
  have hnd : (n : ℝ) * d = 2 * Real.pi := sectorWidth_mul (NeZero.ne n)
  let k := toIcoDiv hd 0 (Complex.arg (z : ℂ))
  have hm := sub_toIcoDiv_zsmul_mem_Ico hd 0 (Complex.arg (z : ℂ))
  rw [zero_add, zsmul_eq_mul] at hm
  let w := Circle.exp (-(k : ℝ) * d)
  have hw : w ^ n = 1 := by
    change Circle.exp (-(k : ℝ) * d) ^ n = 1
    rw [← Circle.exp_nsmul, nsmul_eq_mul]
    apply Circle.exp_eq_one.mpr
    refine ⟨-k, ?_⟩
    push_cast
    rw [← hnd]
    ring
  let r : rootsOfUnity n Circle :=
    rootsOfUnity.mkOfPowEq w hw
  have hr : (r.val : Circle) * z ∈ circleSector n := by
    refine ⟨Complex.arg (z : ℂ) - (k : ℝ) * d, hm, ?_⟩
    rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_arg, ← neg_mul, mul_comm]
    rfl
  refine ⟨r, hr, ?_⟩
  intro s hs
  obtain ⟨x, hx, hxz⟩ := hs
  obtain ⟨y, hy, hyz⟩ := hr
  have hp : Circle.exp ((n : ℝ) * x) = Circle.exp ((n : ℝ) * y) := by
    rw [Circle.exp_natCast_mul, Circle.exp_natCast_mul, hxz, hyz, mul_pow, mul_pow,
      (mem_rootsOfUnity' _ _).mp s.property, (mem_rootsOfUnity' _ _).mp r.property]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hp
  have hxy : x = y + (m : ℝ) * d := by
    apply (mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℝ) ≠ 0))
    calc
      (n : ℝ) * x = (n : ℝ) * y + (m : ℝ) * (2 * Real.pi) := hm
      _ = (n : ℝ) * (y + (m : ℝ) * d) := by rw [← hnd]; ring
  have hy' : y ∈ Ico (0 : ℝ) (0 + d) := by simpa only [zero_add] using hy
  have hx' : x ∈ Ico (0 : ℝ) (0 + d) := by simpa only [zero_add] using hx
  have hdiv : toIcoMod hd 0 x = y := (toIcoMod_eq_iff hd).mpr
    ⟨hy', m, by rwa [zsmul_eq_mul]⟩
  have hEq : x = y := ((toIcoMod_eq_self hd).mpr hx').symm.trans hdiv
  apply Subtype.ext
  apply Units.ext
  rw [← hEq] at hyz
  exact mul_right_cancel (hxz.symm.trans hyz)

/-- The half-open angular sector centered at zero. -/
def centeredPhaseHalfOpen (r : ℝ) : Set Circle :=
  Circle.exp '' Ico (-r) r

/-- Centering the half-open sector preserves its unique root-of-unity reductions. -/
theorem centeredPhaseHalfOpen_unique_rotation (n : ℕ) [NeZero n] (z : Circle) :
    ∃! t : rootsOfUnity n Circle, (t.val : Circle) * z ∈ centeredPhaseHalfOpen (Real.pi / n) := by
  let r := Real.pi / (n : ℝ)
  have he : r + r = 2 * Real.pi / (n : ℝ) := by ring
  have h (x : Circle) : x ∈ centeredPhaseHalfOpen r ↔ Circle.exp r * x ∈ circleSector n := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨r + y, ⟨by linarith [hy.1], ?_⟩, Circle.exp_add r y⟩
      rw [← he]
      exact add_lt_add_right hy.2 r
    · rintro ⟨y, hy, hx⟩
      have hy' : y < r + r := he ▸ hy.2
      refine ⟨y - r, ⟨by linarith [hy.1], by linarith⟩, ?_⟩
      rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, hx, mul_comm (Circle.exp r) x,
        mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨u, hu, huniq⟩ := circleSector_unique_rotation n (Circle.exp r * z)
  refine ⟨u, (h _).mpr (by simpa only [mul_left_comm] using hu), fun t ht => huniq t ?_⟩
  simpa only [mul_left_comm] using (h _).mp ht

/-- The open angles inside the half-open sector. -/
theorem circleSector_hasInterior (n : ℕ) (hn : n ≠ 0) :
    ∃ U : Set Circle, IsOpen U ∧ U.Nonempty ∧ U ⊆ circleSector n := by
  let d := 2 * Real.pi / (n : ℝ)
  have hd : 0 < d := sectorWidth_pos hn
  refine ⟨Circle.exp '' Ioo 0 d, isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo, ?_, ?_⟩
  · exact ⟨Circle.exp (d / 2), ⟨d / 2, ⟨by linarith, by linarith⟩, rfl⟩⟩
  · exact image_mono Ioo_subset_Ico_self


/-- The phase of a nonzero complex number, regarded as a continuous
multiplicative map on complex units. -/
def complexUnitPhase : ℂˣ →* Circle where
  toFun z := ⟨z.val / (‖z.val‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr z.ne_zero)]⟩
  map_one' := by
    apply Subtype.ext
    change (1 : ℂ) / (‖(1 : ℂ)‖ : ℂ) = 1
    simp
  map_mul' x y := by
    apply Subtype.ext
    change x.val * y.val / (‖x.val * y.val‖ : ℂ) =
      (x.val / (‖x.val‖ : ℂ)) * (y.val / (‖y.val‖ : ℂ))
    rw [norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

theorem complexUnitPhase_continuous : Continuous complexUnitPhase := by
  apply Continuous.subtype_mk
  exact Units.continuous_val.div
    (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val))
    (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))

theorem complexUnitPhase_of_norm_one (z : ℂˣ) (h : ‖z.val‖ = 1) :
    (complexUnitPhase z : ℂ) = z.val := by
  change z.val / (‖z.val‖ : ℂ) = z.val
  rw [h, Complex.ofReal_one, div_one]

theorem complexUnitPhase_arg (z : ℂˣ) :
    Complex.arg (complexUnitPhase z : ℂ) = Complex.arg z.val := by
  change Complex.arg (z.val / (‖z.val‖ : ℂ)) = Complex.arg z.val
  rw [div_eq_inv_mul, ← Complex.ofReal_inv]
  exact Complex.arg_real_mul _ (inv_pos.mpr (norm_pos_iff.mpr z.ne_zero))

theorem mem_circleSector_iff_arg {n : ℕ} (hn : 2 ≤ n) (z : Circle) :
    z ∈ circleSector n ↔ Complex.arg (z : ℂ) ∈ Ico 0 (2 * Real.pi / n) := by
  refine ⟨?_, fun h => ⟨_, h, Circle.exp_arg z⟩⟩
  rintro ⟨x, hx, rfl⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 2 * Real.pi / (n : ℝ) ≤ Real.pi := by
    exact (div_le_iff₀ (by linarith)).mpr (by nlinarith [Real.pi_pos])
  rw [Circle.arg_exp (by linarith [hx.1, Real.pi_pos]) (hx.2.le.trans hd)]
  exact hx

end

end Masullo
