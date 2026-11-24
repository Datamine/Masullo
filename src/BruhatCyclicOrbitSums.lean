import BruhatSchwartzDifferences
import ElementarySchwartzCutoffs
import ModulatedBruhatCompactCore
import Mathlib.Analysis.PSeries

open Filter Function Set Topology
open scoped NNReal

namespace Masullo

noncomputable section

set_option maxHeartbeats 850000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem log_mul_zpow (m : G →ₜ* Multiplicative ℝ) (γ x : G) (k : ℤ) :
    (m (γ ^ k * x)).toAdd = (k : ℝ) * (m γ).toAdd + (m x).toAdd := by
  simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul]

/-- A single continuous seminorm on a Bruhat stage controls the logarithmic
decay everywhere on the ambient group, including outside the stage. -/
theorem BruhatSchwartzStage.exists_log_decay_seminorm (p : BruhatSchwartzStage G)
    (m : G →ₜ* Multiplicative ℝ) (N : ℕ) :
    ∃ q : Seminorm ℂ p.Space, Continuous q ∧ ∀ u x,
      (1 + |(m x).toAdd|) ^ N * ‖p.realize u x‖ ≤ q u := by
  let A := ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
  let M := (p.1.descendHom m (p.1.modulation_eq_one_on_kernel m)).comp
    (p.2.equiv.symm : Multiplicative A →ₜ* p.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  obtain ⟨q, hq, hb⟩ := exists_elementary_log_decay_seminorm l hl N
  refine ⟨q, hq, fun u x ↦ ?_⟩
  by_cases hx : x ∈ p.1.upper.val
  · let y : p.1.upper.val := ⟨x, hx⟩
    let z := (p.1.stageCoordinates p.2 y).toAdd
    have hz : l z = (m x).toAdd := by
      change ((p.1.descendHom m (p.1.modulation_eq_one_on_kernel m))
        (p.2.equiv.symm (p.2.equiv (QuotientGroup.mk y)))).toAdd = _
      rw [p.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
    have he : p.realize u x = u z := p.1.realizeSchwartz_apply_of_mem p.2 u y
    simpa only [hz, ← he] using hb u z
  · have he : p.realize u x = 0 := p.1.realizeSchwartz_apply_of_not_mem p.2 u x hx
    simp only [he, norm_zero, mul_zero]
    exact apply_nonneg q u

private def cyclicMajorant (k : ℤ) : ℝ := 1 / (1 + |(k : ℝ)|) ^ 2

private theorem summable_cyclicMajorant : Summable cyclicMajorant := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  have hn : Summable (fun n : ℕ ↦ cyclicMajorant (n : ℤ)) := by
    convert h using 1
    funext n
    simp only [cyclicMajorant, Int.cast_natCast, Real.rpow_two,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rw [add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨hn, hn.congr fun n ↦ by simp [cyclicMajorant]⟩

private theorem stage_orbit_majorant (p : BruhatSchwartzStage G)
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd) (x : G) :
    ∃ q : Seminorm ℂ p.Space, Continuous q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u k, ‖p.realize u (γ ^ k * x)‖ ≤ C * q u * cyclicMajorant k := by
  obtain ⟨q, hq, hb⟩ := p.exists_log_decay_seminorm m 2
  let d := (m γ).toAdd
  let a := (m x).toAdd
  let L := 1 + (1 + |a|) / d
  have hL : 0 ≤ L := by dsimp [L, d]; positivity
  refine ⟨q, hq, L ^ 2, sq_nonneg _, fun u k ↦ ?_⟩
  let t := (m (γ ^ k * x)).toAdd
  have ht : t = (k : ℝ) * d + a := log_mul_zpow m γ x k
  have hsep : |(k : ℝ)| * d ≤ |t| + |a| := by
    calc
      |(k : ℝ)| * d = |(k : ℝ) * d| := by rw [abs_mul, abs_of_pos hγ]
      _ = |t - a| := congrArg abs (by linarith)
      _ ≤ |t| + |a| := abs_sub _ _
  have hratio : |(k : ℝ)| ≤ (|t| + |a|) / d :=
    (le_div_iff₀ hγ).2 hsep
  have hle : 1 + |(k : ℝ)| ≤ L * (1 + |t|) := by
    have hp : 0 ≤ (d + |a|) * |t| := mul_nonneg
      (add_nonneg hγ.le (abs_nonneg a)) (abs_nonneg t)
    apply (mul_le_mul_iff_left₀ hγ).1
    have htdiv : ((|t| + |a|) / d) * d = |t| + |a| := div_mul_cancel₀ _ hγ.ne'
    have hLd : L * d = d + (1 + |a|) := by
      dsimp [L]
      rw [add_mul, one_mul, div_mul_cancel₀ _ hγ.ne']
    calc
      (1 + |(k : ℝ)|) * d ≤ (1 + (|t| + |a|) / d) * d :=
        mul_le_mul_of_nonneg_right (by linarith) hγ.le
      _ = d + (|t| + |a|) := by rw [add_mul, one_mul, htdiv]
      _ ≤ (L * (1 + |t|)) * d := by
        rw [mul_right_comm L, hLd]
        nlinarith [hp]
  have hkpos : 0 < (1 + |(k : ℝ)|) ^ 2 := by positivity
  unfold cyclicMajorant
  rw [mul_one_div, le_div_iff₀ hkpos, mul_comm ‖p.realize u (γ ^ k * x)‖]
  calc
    (1 + |(k : ℝ)|) ^ 2 * ‖p.realize u (γ ^ k * x)‖ ≤
        (L * (1 + |t|)) ^ 2 * ‖p.realize u (γ ^ k * x)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hle _) (norm_nonneg _)
    _ = L ^ 2 * ((1 + |t|) ^ 2 * ‖p.realize u (γ ^ k * x)‖) := by ring
    _ ≤ L ^ 2 * q u := mul_le_mul_of_nonneg_left (hb u _) (sq_nonneg _)

/-- Every cyclic orbit with positive logarithmic period is absolutely summable
for a Schwartz–Bruhat test. -/
theorem bruhatSchwartz_cyclicOrbit_summable_norm
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd)
    (f : BruhatSchwartz G) (x : G) :
    Summable (fun k : ℤ ↦ ‖f.val (γ ^ k * x)‖) := by
  obtain ⟨p, u, hu⟩ := f.property
  obtain ⟨q, _, C, _, hq⟩ := stage_orbit_majorant p m γ hγ x
  rw [← hu]
  exact (summable_cyclicMajorant.mul_left (C * q u)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (hq u)

private def bruhatSchwartz_indexedCyclicOrbitSum (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < (m γ).toAdd) (x : G) {ι : Type*} (j : ι → ℤ) (hj : Injective j) :
    BruhatSchwartz G →L[ℂ] ℂ := by
  have hsum (f : BruhatSchwartz G) : Summable (fun k : ι ↦ ‖f.val (γ ^ j k * x)‖) :=
    (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).comp_injective hj
  have hmaj : Summable (cyclicMajorant ∘ j) := summable_cyclicMajorant.comp_injective hj
  let A : BruhatSchwartz G →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∑' k : ι, f.val (γ ^ j k * x)
      map_add' := fun f g ↦ (hsum f).of_norm.tsum_add (hsum g).of_norm
      map_smul' := fun c f ↦ (tsum_mul_left (a := c)).trans rfl }
  refine ⟨A, (locallyConvexFinal_continuous_iff
    (fun p : BruhatSchwartzStage G ↦ p.inclusion) A).2 fun p ↦ ?_⟩
  obtain ⟨q, hq, C, hC, hb⟩ := stage_orbit_majorant p m γ hγ x
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
  intro i
  let T := ∑' k, cyclicMajorant (j k)
  have hT : 0 ≤ T := tsum_nonneg fun _ ↦ by unfold cyclicMajorant; positivity
  let B : ℝ≥0 := ⟨C * T, mul_nonneg hC hT⟩
  refine Seminorm.continuous_of_le (q := B • q) (hq.const_smul B) fun u ↦ ?_
  change ‖∑' k : ι, p.realize u (γ ^ j k * x)‖ ≤ (C * T) * q u
  have ha := hsum (p.inclusion u)
  calc
    ‖∑' k : ι, p.realize u (γ ^ j k * x)‖ ≤ ∑' k : ι, ‖p.realize u (γ ^ j k * x)‖ :=
      norm_tsum_le_tsum_norm ha
    _ ≤ ∑' k, (C * q u) * cyclicMajorant (j k) :=
      ha.tsum_le_tsum (fun k ↦ hb u (j k)) (hmaj.mul_left _)
    _ = (C * T) * q u := by rw [tsum_mul_left]; ring

/-- Periodization tested at a single coset is a continuous functional for the
actual final locally convex Schwartz–Bruhat topology. -/
def bruhatSchwartz_cyclicOrbitSum (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < (m γ).toAdd) (x : G) : BruhatSchwartz G →L[ℂ] ℂ :=
  bruhatSchwartz_indexedCyclicOrbitSum m γ hγ x id injective_id

/-- The forward tail that inverts the cyclic difference on its range is
continuous at each evaluation point. -/
def bruhatSchwartz_cyclicForwardSum (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < (m γ).toAdd) (x : G) : BruhatSchwartz G →L[ℂ] ℂ :=
  bruhatSchwartz_indexedCyclicOrbitSum m γ hγ x (fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective

theorem bruhatSchwartz_cyclicForwardSum_apply (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < (m γ).toAdd) (x : G) (f : BruhatSchwartz G) :
    bruhatSchwartz_cyclicForwardSum m γ hγ x f = ∑' n : ℕ, f.val (γ ^ n * x) := by
  change (∑' n : ℕ, f.val (γ ^ (n : ℤ) * x)) = _
  simp only [zpow_natCast]

@[simp] theorem bruhatSchwartz_cyclicOrbitSum_apply (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < (m γ).toAdd) (x : G) (f : BruhatSchwartz G) :
    bruhatSchwartz_cyclicOrbitSum m γ hγ x f = ∑' k : ℤ, f.val (γ ^ k * x) := rfl

/-- Fixed shifts of an orbit preserve its periodization. -/
theorem bruhatSchwartz_cyclicOrbitSum_zpow (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < (m γ).toAdd) (x : G) (j : ℤ) (f : BruhatSchwartz G) :
    bruhatSchwartz_cyclicOrbitSum m γ hγ (γ ^ j * x) f =
      bruhatSchwartz_cyclicOrbitSum m γ hγ x f := by
  simp only [bruhatSchwartz_cyclicOrbitSum_apply, ← mul_assoc, ← zpow_add]
  exact (Equiv.addRight j).tsum_eq (fun k : ℤ ↦ f.val (γ ^ k * x))

/-- A cyclic difference has vanishing orbit sum, as does any limit of cyclic differences. -/
theorem closure_bruhatSchwartzDifference_range_subset_commonKernel
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd) :
    closure ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) ⊆
      ⋂ x : G, ((bruhatSchwartz_cyclicOrbitSum m γ hγ x).ker : Set (BruhatSchwartz G)) := by
  have hc : IsClosed (⋂ x : G,
      ((bruhatSchwartz_cyclicOrbitSum m γ hγ x).ker : Set (BruhatSchwartz G))) :=
    isClosed_iInter fun x ↦ (bruhatSchwartz_cyclicOrbitSum m γ hγ x).isClosed_ker
  apply closure_minimal _ hc
  rintro _ ⟨f, rfl⟩
  apply mem_iInter.2
  intro x
  change ∑' k : ℤ, (bruhatSchwartzDifference γ f).val (γ ^ k * x) = 0
  simp_rw [bruhatSchwartzDifference_apply, mul_left_comm γ]
  have hf := (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).of_norm
  have hg := (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f (γ * x)).of_norm
  rw [hf.tsum_sub hg]
  rw [← bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x f,
    ← bruhatSchwartz_cyclicOrbitSum_apply m γ hγ (γ * x) f]
  have he : (γ ^ (1 : ℤ)) * x = γ * x := by rw [zpow_one]
  rw [← congrArg (fun y ↦ bruhatSchwartz_cyclicOrbitSum m γ hγ y f) he,
    bruhatSchwartz_cyclicOrbitSum_zpow, sub_self]

/-- Positive-log-period cyclic differences, and their finite products, are
injective on the full Schwartz–Bruhat space. -/
theorem bruhatSchwartzDifferenceProduct_injective
    (m : G →ₜ* Multiplicative ℝ) (gs : List G)
    (hgs : ∀ g ∈ gs, 0 < (m g).toAdd) :
    Injective (bruhatSchwartzDifferenceProduct gs) := by
  induction gs with
  | nil => exact injective_id
  | cons g gs ih =>
    have hg := hgs g (.head _)
    have hsingle : Injective (bruhatSchwartzDifference g) := by
      apply (bruhatSchwartzDifference g).toLinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro f hf
      apply Subtype.ext
      funext x
      have hd : ∀ y, f.val (g * y) = f.val y := fun y ↦
        (sub_eq_zero.mp ((bruhatSchwartzDifference_apply g f y).symm.trans
          (congrArg (fun v : BruhatSchwartz G ↦ v.val y) hf))).symm
      have hp (n : ℕ) : f.val (g ^ n * x) = f.val x := by
        induction n with
        | zero => simp
        | succ n hn => rw [pow_succ', mul_assoc, hd, hn]
      have hb := (bruhatSchwartz_cyclicOrbit_summable_norm m g hg f x).comp_injective
        (fun _ _ h ↦ Int.ofNat_inj.mp h)
      change Summable (fun n : ℕ ↦ ‖f.val (g ^ (n : ℤ) * x)‖) at hb
      simp only [zpow_natCast, hp] at hb
      have hl := hb.tendsto_atTop_zero
      exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hl)
    exact hsingle.comp (ih (fun a ha ↦ hgs a (.tail _ ha)))

/-- A vanishing cyclic orbit sum gives two equivalent formulas for the
pointwise inverse. The backward formula starts one step behind the base point. -/
theorem bruhatSchwartz_cyclicDifference_two_tails
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd)
    (f : BruhatSchwartz G) (hzero : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0) :
    let u (x : G) := ∑' n : ℕ, f.val (γ ^ n * x)
    (∀ x, u x = -(∑' n : ℕ, f.val (γ ^ (-(n : ℤ) - 1) * x))) ∧
    ∀ x, u x - u (γ * x) = f.val x := by
  dsimp only
  constructor
  · intro x
    let F (n : ℤ) := f.val (γ ^ n * x)
    have hF : Summable F := (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).of_norm
    have hpos : Summable (fun n : ℕ ↦ F (n : ℤ)) :=
      hF.comp_injective Nat.cast_injective
    have hneg : Summable (fun n : ℕ ↦ F (-((n : ℤ) + 1))) :=
      hF.comp_injective (fun a b h ↦ by exact_mod_cast (by omega : (a : ℤ) = b))
    have h := (hzero x).symm.trans (tsum_of_nat_of_neg_add_one hpos hneg)
    have he (n : ℕ) : -((n : ℤ) + 1) = -(n : ℤ) - 1 := by ring
    simpa only [F, he, id_eq, zpow_natCast] using eq_neg_of_add_eq_zero_left h.symm
  · intro x
    have hnat : Summable (fun n : ℕ ↦ f.val (γ ^ n * x)) := by
      simpa only [comp_def, zpow_natCast] using
        (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).of_norm.comp_injective
          (Nat.cast_injective (R := ℤ))
    rw [hnat.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, pow_succ, mul_assoc, add_sub_cancel_right]

/-- Compact-source exactness for cyclic differences. The solution belongs to the
actual Schwartz–Bruhat space and is supported in the sharper logarithmic collar. -/
theorem bruhatSchwartz_cyclicDifference_compact_source
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (γ : G) (hγ : 0 < (m γ).toAdd) (f : BruhatSchwartz G) (a b : ℝ)
    (hf : support f.val ⊆ (fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
    (hzero : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0) :
    ∃ v : BruhatSchwartz G,
      support v.val ⊆ (fun x ↦ (m x).toAdd) ⁻¹' Icc (a + (m γ).toAdd) b ∧
      HasCompactSupport v.val ∧ bruhatSchwartzDifference γ v = f := by
  let d := (m γ).toAdd
  let t (x : G) := (m x).toAdd
  let u (x : G) := ∑' n : ℕ, f.val (γ ^ n * x)
  have hlog (k : ℤ) (x : G) : t (γ ^ k * x) = (k : ℝ) * d + t x :=
    log_mul_zpow m γ x k
  have hlogNat (n : ℕ) (x : G) : t (γ ^ n * x) = (n : ℝ) * d + t x := by
    simpa only [zpow_natCast, Int.cast_natCast] using hlog (n : ℤ) x
  have hu := bruhatSchwartz_cyclicDifference_two_tails m γ hγ f hzero
  have hs : support u ⊆ t ⁻¹' Icc (a + d) b := by
    intro x hx
    constructor
    · by_contra! h
      have hz (n : ℕ) : f.val (γ ^ (-(n : ℤ) - 1) * x) = 0 := by
        by_contra hn
        have he := (hf hn).1
        change a ≤ t (γ ^ (-(n : ℤ) - 1) * x) at he
        rw [hlog] at he
        push_cast at he
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hγ.le]
      exact hx ((hu.1 x).trans (by simp only [hz, tsum_zero, neg_zero]))
    · by_contra! h
      have hz (n : ℕ) : f.val (γ ^ n * x) = 0 := by
        by_contra hn
        have he := (hf hn).2
        change t (γ ^ n * x) ≤ b at he
        rw [hlogNat] at he
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hγ.le]
      exact hx (by simp only [u, hz, tsum_zero])
  obtain ⟨N, hN⟩ := exists_nat_gt (max |a + d| |b|)
  let R := 2 * ((N : ℝ) + 1)
  obtain ⟨M, hM⟩ := exists_nat_gt ((b + R) / d)
  let w : BruhatSchwartz G := ∑ n ∈ Finset.range M, bruhatSchwartz_translate ((γ ^ n)⁻¹) f
  have hw (x : G) : w.val x = ∑ n ∈ Finset.range M, f.val (γ ^ n * x) := by
    change (bruhatSchwartzSubmodule.subtype (∑ n ∈ Finset.range M,
      bruhatSchwartz_translate ((γ ^ n)⁻¹) f)) x = _
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun n _ ↦ by
      change (bruhatSchwartz_translate ((γ ^ n)⁻¹) f).val x = _
      rw [bruhatSchwartz_translate_apply, inv_inv]
  have hfinite (x : G) (hx : |t x| ≤ R) : w.val x = u x := by
    have hz (n : ℕ) : f.val (γ ^ (n + M) * x) = 0 := by
      by_contra hn
      have he := (hf hn).2
      change t (γ ^ (n + M) * x) ≤ b at he
      rw [hlogNat, Nat.cast_add] at he
      have hMd : b + R < (M : ℝ) * d := (div_lt_iff₀ hγ).1 hM
      nlinarith [(abs_le.1 hx).1, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hγ.le]
    have hnat : Summable (fun n : ℕ ↦ f.val (γ ^ n * x)) := by
      simpa only [comp_def, zpow_natCast] using
        (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).of_norm.comp_injective
          (Nat.cast_injective (R := ℤ))
    simpa only [hz, tsum_zero, add_zero, hw] using hnat.sum_add_tsum_nat_add M
  obtain ⟨v, _, hv, hc⟩ := exists_bruhatSchwartz_logCutoff_sequence m hm w
  have he (x : G) : (v N).val x = u x := by
    have hsN : x ∈ support u → |t x| < (N : ℝ) + 1 := by
      intro hx
      have hb := hs hx
      change a + d ≤ t x ∧ t x ≤ b at hb
      rw [abs_lt]
      have ha := (le_max_left |a + d| |b|).trans_lt hN
      have hc := (le_max_right |a + d| |b|).trans_lt hN
      constructor <;> linarith [(abs_lt.1 ha).1, (abs_lt.1 hc).2, hb.1, hb.2]
    rw [hv N x]
    change truncationMultiplier N (t x) * w.val x = u x
    by_cases hx : |t x| ≤ R
    · rw [hfinite x hx]
      by_cases hu : u x = 0
      · rw [hu, mul_zero]
      · rw [truncationMultiplier_one N (hsN hu), one_mul]
    · rw [truncationMultiplier_zero N (lt_of_not_ge hx), zero_mul]
      by_contra hn
      exact hx ((hsN (Ne.symm hn)).le.trans (by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) N]))
  refine ⟨v N, fun x hx ↦ hs (fun h ↦ hx ((he x).trans h)), hc N, ?_⟩
  apply Subtype.ext
  funext x
  rw [bruhatSchwartzDifference_apply, he, he]
  exact hu.2 x

/-- On compactly supported inputs, the orbit-sum kernel is exactly the range
of the difference operator on compactly supported Schwartz–Bruhat tests. -/
theorem bruhatSchwartz_cyclicOrbitSum_zero_iff_compact_difference
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (γ : G) (hγ : 0 < (m γ).toAdd) (f : BruhatSchwartz G) (hf : HasCompactSupport f.val) :
    (∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0) ↔
      ∃ v : BruhatSchwartz G, HasCompactSupport v.val ∧ bruhatSchwartzDifference γ v = f := by
  constructor
  · intro hzero
    let t (x : G) := (m x).toAdd
    have ht : Continuous t := continuous_toAdd.comp m.continuous
    have hc := hf.isCompact.image ht
    obtain ⟨a, ha⟩ := hc.bddBelow
    obtain ⟨b, hb⟩ := hc.bddAbove
    have hf' : support f.val ⊆ t ⁻¹' Icc a b := by
      intro x hx
      have hx' : t x ∈ t '' tsupport f.val := mem_image_of_mem t (subset_closure hx)
      exact ⟨ha hx', hb hx'⟩
    obtain ⟨v, _, hv, h⟩ := bruhatSchwartz_cyclicDifference_compact_source m hm γ hγ f a b hf' hzero
    exact ⟨v, hv, h⟩
  · rintro ⟨v, _, hv⟩ x
    have hfRange : f ∈ ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) := ⟨v, hv⟩
    exact mem_iInter.mp
      (closure_bruhatSchwartzDifference_range_subset_commonKernel m γ hγ (subset_closure hfRange)) x

end

end Masullo
