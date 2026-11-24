import Mathlib.Analysis.InnerProductSpace.l2Space

open Filter Function Set Topology
open scoped ENNReal

noncomputable section

namespace Masullo

namespace BlockBasis

abbrev H := lp (fun _ : ℕ × Bool => ℂ) 2

def e (n : ℕ) (side : Bool) : H := lp.single 2 (n, side) 1

private theorem norm_e (n : ℕ) (side : Bool) : ‖e n side‖ = 1 := by
  simp [e, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

private def epsilon (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by
  unfold epsilon
  positivity

private def raw (n : ℕ) : H := e n false + (epsilon n : ℂ) • e n true

private theorem raw_apply (n m : ℕ) (side : Bool) :
    raw n (m, side) = if m = n then (if side then (epsilon n : ℂ) else 1) else 0 := by
  change e n false (m, side) + (epsilon n : ℂ) * e n true (m, side) = _
  cases side <;> by_cases h : m = n <;> simp [e, lp.single_apply, h]

private theorem raw_ne_zero (n : ℕ) : raw n ≠ 0 := by
  intro h
  have h' := congrArg (fun x : H => x (n, false)) h
  simp [raw_apply] at h'

/-- In each two-coordinate block the two normalized vectors become nearly
parallel as the block index grows. -/
def vec (p : ℕ × Bool) : H :=
  if p.2 then (‖raw p.1‖ : ℂ)⁻¹ • raw p.1 else e p.1 false

theorem norm_vec (p : ℕ × Bool) : ‖vec p‖ = 1 := by
  rcases p with ⟨n, side⟩
  cases side
  · exact norm_e n false
  · simp only [vec, ite_true, norm_smul, norm_inv, Complex.norm_real]
    rw [Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (raw_ne_zero n))]

private def eval (n : ℕ) (side : Bool) : H →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ × Bool => ℂ) (p := 2) (n, side)

/-- The coordinate functionals are continuous individually, but there is no
uniform bound of the kind supplied by a Schauder basis. -/
def coord (p : ℕ × Bool) : H →L[ℂ] ℂ :=
  if p.2 then ((‖raw p.1‖ : ℂ) / (epsilon p.1 : ℂ)) • eval p.1 true
  else eval p.1 false - (epsilon p.1 : ℂ)⁻¹ • eval p.1 true

@[simp] private theorem eval_apply (n : ℕ) (side : Bool) (x : H) :
    eval n side x = x (n, side) := rfl

theorem biorthogonal (p q : ℕ × Bool) :
    coord p (vec q) = if p = q then 1 else 0 := by
  have hep (n : ℕ) : (epsilon n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (epsilon_pos n).ne'
  have hr (n : ℕ) : (‖raw n‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (raw_ne_zero n))
  rcases p with ⟨m, s⟩
  rcases q with ⟨n, t⟩
  cases s <;> cases t <;> by_cases h : m = n
  all_goals simp [coord, vec, raw_apply, e, lp.single_apply, h, hep, hr]

theorem coordinates_separate (x : H) (hx : ∀ p, coord p x = 0) : x = 0 := by
  apply Subtype.ext
  funext p
  rcases p with ⟨n, side⟩
  have hr : (‖raw n‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (raw_ne_zero n))
  have hep : (epsilon n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (epsilon_pos n).ne'
  have htrue : x (n, true) = 0 := by
    have h := hx (n, true)
    change ((‖raw n‖ : ℂ) / (epsilon n : ℂ)) * x (n, true) = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (div_ne_zero hr hep)
  cases side
  · have h := hx (n, false)
    change x (n, false) - (epsilon n : ℂ)⁻¹ * x (n, true) = 0 at h
    simpa [htrue] using h
  · exact htrue

private theorem raw_eq_scaled_vec (n : ℕ) : raw n = (‖raw n‖ : ℂ) • vec (n, true) := by
  simp [vec, smul_smul, mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (raw_ne_zero n)))]

theorem span_dense : Dense (Submodule.span ℂ (range vec) : Set H) := by
  let L := Submodule.span ℂ (range vec)
  have he₀ (n : ℕ) : e n false ∈ L := Submodule.subset_span (mem_range_self (n, false))
  have he₁ (n : ℕ) : e n true ∈ L := by
    have hraw : raw n ∈ L := by
      rw [raw_eq_scaled_vec]
      exact L.smul_mem _ (Submodule.subset_span (mem_range_self (n, true)))
    have heps : (epsilon n : ℂ) • e n true ∈ L := by
      have h := L.sub_mem hraw (he₀ n)
      simpa only [raw, add_sub_cancel_left] using h
    have h := L.smul_mem (epsilon n : ℂ)⁻¹ heps
    rwa [smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (epsilon_pos n).ne'), one_smul] at h
  have hsingle (x : H) (p : ℕ × Bool) : lp.single 2 p (x p) ∈ L := by
    have he : e p.1 p.2 ∈ L := by cases p.2 <;> tauto
    have h := L.smul_mem (x p) he
    have heq : (x p) • e p.1 p.2 = lp.single 2 p (x p) := by
      change (x p) • lp.single (E := fun _ : ℕ × Bool => ℂ) 2 p 1 = _
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rwa [heq] at h
  intro x
  have hs := lp.hasSum_single (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x
  exact isClosed_closure.mem_of_tendsto hs (Eventually.of_forall fun s =>
    subset_closure (L.sum_mem fun i _ => hsingle x i))

def order (n : ℕ) : ℕ × Bool := (n / 2, n % 2 == 1)

private theorem order_even (n : ℕ) : order (2 * n) = (n, false) := by
  simp [order, Nat.mul_comm]

private theorem order_odd (n : ℕ) : order (2 * n + 1) = (n, true) := by
  apply Prod.ext
  · change (2 * n + 1) / 2 = n
    omega
  · change ((2 * n + 1) % 2 == 1) = true
    rw [beq_iff_eq]
    omega

/-- In the natural block ordering this normalized Markushevich family is no
Schauder basis. The partial projection cutting block n has norm ≥ n+1. -/
theorem not_schauder_in_block_order :
    ¬ ∃ b : SchauderBasis ℂ H, ∀ n, b n = vec (order n) := by
  rintro ⟨b, hb⟩
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  let P := b.proj (2 * n + 1)
  have heven : b (2 * n) = e n false := by rw [hb, order_even]; rfl
  have hodd : b (2 * n + 1) = vec (n, true) := by rw [hb, order_odd]
  have hfix : P (e n false) = e n false := by
    rw [← heven]
    exact (b.proj_apply_basis_mem _ _).trans (ite_eq_left (by omega))
  have hkill : P (raw n) = 0 := by
    rw [raw_eq_scaled_vec, ← hodd, map_smul]
    change (‖raw n‖ : ℂ) • b.proj (2 * n + 1) (b (2 * n + 1)) = 0
    rw [b.proj_apply_basis_mem, ite_eq_right (lt_irrefl _), smul_zero]
  have hP : P ((epsilon n : ℂ) • e n true) = -e n false := by
    have h := congrArg P (show raw n - e n false = (epsilon n : ℂ) • e n true by
      unfold raw
      abel)
    rw [map_sub, hkill, hfix, zero_sub] at h
    exact h.symm
  have bound := P.le_opNorm ((epsilon n : ℂ) • e n true)
  rw [hP, norm_neg, norm_e, norm_smul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (epsilon_pos n).le] at bound
  have hle : 1 ≤ C * epsilon n :=
    bound.trans (mul_le_mul_of_nonneg_right (hC _) (epsilon_pos n).le)
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hcon := (le_div_iff₀ hp).mp (by simpa [epsilon, div_eq_mul_inv] using hle)
  linarith

private theorem order_surjective : Surjective order := by
  rintro ⟨n, side⟩
  cases side
  · exact ⟨2 * n, order_even n⟩
  · exact ⟨2 * n + 1, order_odd n⟩

private theorem order_injective : Injective order := by
  intro a b hab
  have hquot := congrArg Prod.fst hab
  change a / 2 = b / 2 at hquot
  have hrem := congrArg Prod.snd hab
  change (a % 2 == 1) = (b % 2 == 1) at hrem
  have hh (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hh a with ha | ha <;> rcases hh b with hb | hb
  · omega
  · simp [ha, hb] at hrem
  · simp [ha, hb] at hrem
  · omega

/-- The normalized, fundamental and total biorthogonal sequence required by
the Markushevich hypothesis of Lemma 10.4.2.5, with its Schauder conclusion false. -/
theorem exists_normalized_markushevich_not_schauder :
    ∃ (x : ℕ → H) (φ : ℕ → H →L[ℂ] ℂ),
      (∀ n, ‖x n‖ = 1) ∧
      (∀ m n, φ m (x n) = if m = n then 1 else 0) ∧
      Dense (Submodule.span ℂ (range x) : Set H) ∧
      (∀ v, (∀ n, φ n v = 0) → v = 0) ∧
      ¬ ∃ b : SchauderBasis ℂ H, ∀ n, b n = x n := by
  refine ⟨vec ∘ order, coord ∘ order, fun n => norm_vec (order n), ?_, ?_, ?_,
    not_schauder_in_block_order⟩
  · intro m n
    change coord (order m) (vec (order n)) = _
    rw [biorthogonal]
    by_cases h : m = n
    · simp [h]
    · have hh : order m ≠ order n := fun he => h (order_injective he)
      rw [ite_eq_right hh, ite_eq_right h]
  · rw [range_comp, order_surjective.range_eq, image_univ]
    exact span_dense
  · intro v hv
    apply coordinates_separate v
    intro p
    obtain ⟨n, rfl⟩ := order_surjective p
    exact hv n

end BlockBasis

/-- The missing sufficient condition in the attempted upgrade to a Schauder
basis: bounded partial projections together with a dense biorthogonal span. -/
def schauderOfBoundedBiorthogonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : ℕ → E) (φ : ℕ → E →L[ℂ] ℂ)
    (horth : ∀ i j, φ i (v j) = (Pi.single j (1 : ℂ) : ℕ → ℂ) i)
    (hdense : Dense (Submodule.span ℂ (range v) : Set E))
    (C : ℝ) (hP : ∀ n, ‖∑ i ∈ Finset.range n, (φ i).smulRight (v i)‖ ≤ C) :
    SchauderBasis ℂ E := by
  classical
  let P (n : ℕ) : E →L[ℂ] E := ∑ i ∈ Finset.range n, (φ i).smulRight (v i)
  have h₀ : 0 ≤ C := (norm_nonneg (P 0)).trans (hP 0)
  have hv (j : ℕ) : ∀ᶠ n in atTop, P n (v j) = v j := by
    filter_upwards [eventually_ge_atTop (j + 1)] with n hn
    have hj : j ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    change (∑ i ∈ Finset.range n, (φ i).smulRight (v i)) (v j) = _
    simp [horth, Pi.single_apply, Finset.sum_ite_eq', hj]
  have hspan : ∀ y ∈ Submodule.span ℂ (range v), ∀ᶠ n in atTop, P n y = y := by
    intro y hy
    apply Submodule.span_induction (p := fun y _ => ∀ᶠ n in atTop, P n y = y) _ _ _ _ hy
    · rintro _ ⟨j, rfl⟩
      exact hv j
    · exact Eventually.of_forall fun _ => map_zero _
    · intro a b _ _ ha hb
      filter_upwards [ha, hb] with n hna hnb
      simp [hna, hnb]
    · intro c a _ ha
      filter_upwards [ha] with n hna
      simp [hna]
  refine ⟨v, φ, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · simpa [Pi.single_apply, h] using horth i j
    · simpa [Pi.single_apply, h] using horth i j
  intro x
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  have hb : Tendsto (fun n => P n x) atTop (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hC : 0 < C + 1 := by linarith
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x) (ε / (C + 1)) (by positivity)
    filter_upwards [hspan y hy] with n hn
    rw [dist_eq_norm] at hxy ⊢
    have he : P n x - x = P n (x - y) + (y - x) := by
      rw [map_sub, hn]
      abel
    have hbound : ‖P n (x - y)‖ ≤ C * ‖x - y‖ :=
      ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg _))
    rw [he]
    calc
      _ ≤ ‖P n (x - y)‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ C * ‖x - y‖ + ‖x - y‖ := by rw [norm_sub_rev y x]; gcongr
      _ = ‖x - y‖ * (C + 1) := by ring
      _ < ε := (lt_div_iff₀ hC).mp hxy
  change Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (φ i) x • v i) atTop (𝓝 x)
  simpa only [P, sum_apply, ContinuousLinearMap.smulRight_apply] using hb

end Masullo
