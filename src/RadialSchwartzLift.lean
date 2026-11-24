import SchwartzFlatExtension
import ExponentialDecayStructure

open Filter Function Set Topology
open scoped Classical ContDiff SchwartzMap

namespace Masullo

noncomputable section

/-- On a positive-dilation-invariant open set, dilation has its expected
exact effect on the norm of every Fréchet jet. -/
theorem norm_iteratedFDeriv_comp_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (hscale : ∀ x : E, r • x ∈ U ↔ x ∈ U)
    (g : E → ℂ) (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ g (r • y)) x‖ =
      r ^ j * ‖iteratedFDeriv ℝ j g (r • x)‖ := by
  let R : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
  have hrx : R x ∈ U := (hscale x).mpr hx
  have hRU : R ⁻¹' U = U := Set.ext hscale
  have he := R.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn
    (hRU.symm ▸ hU.uniqueDiffOn) hrx (i := j) (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  rw [hRU, iteratedFDerivWithin_of_isOpen j hU hx, iteratedFDerivWithin_of_isOpen j hU hrx] at he
  have hcomp : (iteratedFDeriv ℝ j g (R x)).compContinuousLinearMap (fun _ ↦ R) =
      (r ^ j) • iteratedFDeriv ℝ j g (R x) := by
    ext v
    change (iteratedFDeriv ℝ j g (R x)) (fun i ↦ r • v i) =
      r ^ j • (iteratedFDeriv ℝ j g (R x)) v
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp
  rw [hcomp] at he
  change ‖iteratedFDeriv ℝ j (g ∘ R) x‖ = r ^ j * ‖iteratedFDeriv ℝ j g (R x)‖
  simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg hr.le j)] using congrArg norm he

/-- The all-exponent log-Schwartz condition gives an exponential bound on
each bounded set of derivative orders, simultaneously at both ends. -/
theorem logSchwartz_allExponent_jet_bound (f : PositiveRealExponentialDecay univ)
    (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j f.val t‖ ≤ C * Real.exp (-a * |t|) := by
  obtain ⟨_, hp, hn⟩ := (logExponentialDecay_mem_iff_twoSided f.val).mp f.property
  choose P hP hpb using fun j ↦ hp j a ha
  choose N hN hnb using fun j ↦ hn j a ha
  let B (j : ℕ) := P j + N j
  have hB (j : ℕ) : 0 ≤ B j := add_nonneg (hP j) (hN j)
  let C := ∑ i ∈ Finset.range (n + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ hB i
  refine ⟨C, hC, fun j hj t ↦ ?_⟩
  have hjC : B j ≤ C := Finset.single_le_sum (fun i _ ↦ hB i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rcases le_total 0 t with ht | ht
  · have he := hpb j t (by simpa only [one_mul] using ht)
    rw [one_mul] at he
    rw [abs_of_nonneg ht]
    exact he.trans (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right (hN j)).trans hjC) (Real.exp_nonneg _))
  · have he := hnb j t (by simpa only [neg_one_mul] using neg_nonneg.mpr ht)
    rw [neg_one_mul] at he
    rw [abs_of_nonpos ht]
    exact he.trans (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left (hP j)).trans hjC) (Real.exp_nonneg _))

/-- A shift of the profile by a bounded amount preserves its jet bound
with a uniform constant. -/
theorem logSchwartz_allExponent_jet_bound_shifted (f : PositiveRealExponentialDecay univ)
    (n : ℕ) (a L : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s t : ℝ, |s| ≤ L →
      ‖iteratedFDeriv ℝ j f.val (t + s)‖ ≤ C * Real.exp (-a * |t|) := by
  obtain ⟨C, hC, hb⟩ := logSchwartz_allExponent_jet_bound f n a ha
  refine ⟨C * Real.exp (a * L), by positivity, fun j hj s t hs ↦ (hb j hj _).trans ?_⟩
  have ht : |t| ≤ |t + s| + |s| := by
    simpa only [add_sub_cancel_right, sub_zero, zero_sub, abs_neg] using abs_sub_le (t+s) 0 s
  have h : -a * |t+s| ≤ a * L + -a * |t| := by
    have hs' : |t| ≤ |t+s| + L := ht.trans (by gcongr)
    nlinarith
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hC

private theorem compact_jet_bound {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D] {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : E → D) (hg : ContDiffOn ℝ ∞ g U) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ j g x‖ ≤ C := by
  have he (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j g x‖ ≤ B := by
    have hc : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j g x‖) K := by
      apply ((hg.continuousOn_iteratedFDerivWithin
        (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞) hU.uniqueDiffOn).norm.mono hKU).congr
      intro x hx
      change ‖iteratedFDeriv ℝ j g x‖ = ‖iteratedFDerivWithin ℝ j g U x‖
      exact congrArg norm ((iteratedFDerivWithin_of_isOpen j hU (hKU hx)).symm)
    obtain ⟨B, hB⟩ := hK.bddAbove_image hc
    exact ⟨max B 0, le_max_right _ _, fun x hx ↦ (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hbb using he
  let C := ∑ j ∈ Finset.range (n+1), B j
  refine ⟨C + 1, by have : 0 ≤ C := Finset.sum_nonneg (fun j _ ↦ hB j); linarith, ?_⟩
  intro j hj x hx
  exact (hbb j x hx).trans ((Finset.single_le_sum (fun i _ ↦ hB i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans (le_add_of_nonneg_right zero_le_one))

/-- The jets of a bounded-direction modulation of a translated log-Schwartz
profile retain every exponential decay rate in the translation parameter. -/
theorem logSchwartz_comp_mul_jet_bound_on_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (b : E → ℂ) (hb : ContDiffOn ℝ ∞ b U) (l : E → ℝ) (hl : ContDiffOn ℝ ∞ l U)
    (f : PositiveRealExponentialDecay univ) (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (fun y ↦ b y * f.val (t + l y)) x‖ ≤ C * Real.exp (-a * |t|) := by
  obtain ⟨B, hB, hBb⟩ := compact_jet_bound hU hK hKU b hb n
  obtain ⟨D, hD, hDb⟩ := compact_jet_bound hU hK hKU l hl n
  have hlog (x : E) (hx : x ∈ K) : |l x| ≤ D := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hDb 0 (Nat.zero_le _) x hx
  obtain ⟨A, hA, hAb⟩ := logSchwartz_allExponent_jet_bound_shifted f n a D ha
  obtain ⟨g, hgf⟩ := ((logExponentialDecay_mem_iff_twoSided f.val).mp f.property).1
  have hdiff : ContDiff ℝ ∞ f.val := by
    change (g : ℝ → ℂ) = f.val at hgf
    rw [← hgf]
    exact g.smooth'
  let c (j : ℕ) : ℝ := (j.factorial : ℝ) * A * D ^ j
  let C : ℝ := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * B * c (n-j)
  have hC : 0 ≤ C := by
    dsimp [C, c]
    exact Finset.sum_nonneg fun _ _ ↦ by positivity
  refine ⟨C, hC, fun t x hx ↦ ?_⟩
  let u (s : ℝ) := f.val (t + s)
  have hu : ContDiff ℝ ∞ u := hdiff.comp (contDiff_const.add contDiff_id)
  have hcomp (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (u ∘ l) x‖ ≤ c j * Real.exp (-a * |t|) := by
    have ht := norm_iteratedFDerivWithin_comp_le hu.contDiffOn hl
      (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞) uniqueDiffOn_univ hU.uniqueDiffOn
      (mapsTo_univ _ _) (hKU hx)
      (C := A * Real.exp (-a * |t|)) (D := D)
      (fun i hi ↦ by
        rw [iteratedFDerivWithin_univ, iteratedFDeriv_comp_add_left]
        exact hAb i (hi.trans hj) (l x) t (hlog x hx))
      (fun i hi hj' ↦ by
        rw [iteratedFDerivWithin_of_isOpen i hU (hKU hx)]
        exact (hDb i (hj'.trans hj) x hx).trans (le_self_pow₀ hD (by omega)))
    rw [iteratedFDerivWithin_of_isOpen j hU (hKU hx)] at ht
    exact ht.trans_eq (by dsimp [c]; ring)
  have hprod := norm_iteratedFDerivWithin_mul_le hb
    (hu.comp_contDiffOn hl) hU.uniqueDiffOn (hKU hx)
    (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at hprod
  refine hprod.trans ?_
  change _ ≤ (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * B * c (n-j)) * Real.exp (-a * |t|)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (n.choose j : ℝ) * B * (c (n-j) * Real.exp (-a * |t|)) := by
      gcongr
      · exact hBb j hjn x hx
      · exact hcomp _ (Nat.sub_le _ _)
    _ = _ := by rw [mul_assoc ((n.choose j : ℝ) * B)]

private theorem continuous_homogeneous_radius_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (ρ : E → ℝ) (hc : Continuous ρ)
    (hscale : ∀ r : ℝ, 0 < r → ∀ x : E, ρ (r • x) = r * ρ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ρ x ≤ C * ‖x‖ := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).bddAbove_image hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x = 0
  · subst x
    have h := hscale 2 (by norm_num) 0
    rw [smul_zero] at h
    simp only [norm_zero, mul_zero]
    linarith
  · let r := ‖x‖
    have hr : 0 < r := norm_pos_iff.mpr hx
    let y := r⁻¹ • x
    have hy : y ∈ Metric.sphere (0 : E) 1 := by
      simp [y, norm_smul, r, norm_ne_zero_iff.mpr hx]
    have hxy : r • y = x := by simp [y, smul_smul, hr.ne']
    have ht : ρ x = r * ρ y := by rw [← hxy, hscale _ hr]
    rw [ht, mul_comm (max C 0)]
    exact mul_le_mul_of_nonneg_left ((hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)) hr.le

private theorem exp_log_decay_two_bounds (r d : ℝ) (hr : 0 < r) (hd : 0 < d) (m : ℕ) :
    Real.exp (-((m : ℝ) / d) * |d * Real.log r|) ≤ r ^ m ∧
    Real.exp (-((m : ℝ) / d) * |d * Real.log r|) ≤ (r ^ m)⁻¹ := by
  have he : -((m : ℝ) / d) * |d * Real.log r| = -(m : ℝ) * |Real.log r| := by
    rw [abs_mul, abs_of_pos hd]
    field_simp
  rw [he]
  constructor
  · calc
      _ ≤ Real.exp ((m : ℝ) * Real.log r) := Real.exp_le_exp.mpr (by
        nlinarith [neg_abs_le (Real.log r), Nat.cast_nonneg (α := ℝ) m])
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hr]
  · calc
      _ ≤ Real.exp (-((m : ℝ) * Real.log r)) := Real.exp_le_exp.mpr (by
        nlinarith [le_abs_self (Real.log r), Nat.cast_nonneg (α := ℝ) m])
      _ = _ := by rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr]

/-- A compact transverse cutoff lifts an all-exponent logarithmic
Schwartz profile along the rays of a nonnegative homogeneous radius.
The lift is a Schwartz test flat on the zero set of the radius. -/
theorem exists_flatSchwartz_of_logRadius {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (ρ : E → ℝ) (hρ : Continuous ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hscale : ∀ r : ℝ, 0 < r → ∀ x : E, ρ (r • x) = r * ρ x)
    (hs : ContDiffOn ℝ ∞ ρ {x | 0 < ρ x})
    (ψ : 𝓢(E, ℂ)) (hψ : HasCompactSupport ψ) (hK : tsupport ψ ⊆ {x | 0 < ρ x})
    (d : ℝ) (hd : 0 < d) (f : PositiveRealExponentialDecay univ) :
    ∃ g : 𝓢(E, ℂ), g ∈ schwartzFlatSubspace {x | ρ x = 0} ∧
      ∀ x, g x = ψ ((ρ x)⁻¹ • x) * f.val (d * Real.log (ρ x)) := by
  let U := {x : E | 0 < ρ x}
  let K := tsupport ψ
  let q (x : E) := (ρ x)⁻¹ • x
  let b := (ψ : E → ℂ) ∘ q
  let l (x : E) := d * Real.log (ρ x)
  let G (t : ℝ) (x : E) := b x * f.val (t + l x)
  have hU : IsOpen U := isOpen_lt continuous_const hρ
  have h0 : ρ 0 = 0 := by
    have he := hscale 2 (by norm_num) 0
    rw [smul_zero] at he
    linarith
  have hψ0 : ψ 0 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have he : 0 < ρ 0 := hK h
    rw [h0] at he
    exact (lt_irrefl _) he
  have hq : ContDiffOn ℝ ∞ q U := (hs.inv (fun _ hx ↦ (show 0 < ρ _ from hx).ne')).smul contDiffOn_id
  have hb : ContDiffOn ℝ ∞ b U := ψ.smooth'.comp_contDiffOn hq
  have hl : ContDiffOn ℝ ∞ l U :=
    contDiffOn_const.mul (hs.log fun _ hx ↦ (show 0 < ρ _ from hx).ne')
  obtain ⟨f₀, hgf⟩ := ((logExponentialDecay_mem_iff_twoSided f.val).mp f.property).1
  have hf : ContDiff ℝ ∞ f.val := by
    change (f₀ : ℝ → ℂ) = f.val at hgf
    rw [← hgf]
    exact f₀.smooth'
  have hG (t : ℝ) : ContDiffOn ℝ ∞ (G t) U :=
    hb.mul (hf.comp_contDiffOn (contDiffOn_const.add hl))
  obtain ⟨C, hC⟩ := hψ.bddAbove_image continuous_norm.continuousOn
  let A := max C 1
  have hA : 0 ≤ A := zero_le_one.trans (le_max_right _ _)
  have hAb (x : E) (hx : q x ∈ K) : ‖q x‖ ≤ A :=
    (hC ⟨q x, hx, rfl⟩).trans (le_max_left _ _)
  have hrad (x : E) (hx : x ∈ U) : ρ x • q x = x := by
    have hne : ρ x ≠ 0 := (show 0 < ρ x from hx).ne'
    simp [q, smul_smul, hne]
  have hbound (x : E) (hx : x ∈ U) (hqk : q x ∈ K) : ‖x‖ ≤ A * ρ x := by
    have hr : 0 < ρ x := hx
    calc
      ‖x‖ = ‖ρ x • q x‖ := congrArg norm (hrad x hx).symm
      _ = ρ x * ‖q x‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
      _ ≤ A * ρ x := by rw [mul_comm A]; exact mul_le_mul_of_nonneg_left (hAb x hqk) hr.le
  have hTC (t : ℝ) : tsupport (G t) ⊆ {x | ‖x‖ ≤ A * ρ x} := by
    apply closure_minimal _ (isClosed_le continuous_norm (continuous_const.mul hρ))
    intro x hx
    have hb₀ : ψ (q x) ≠ 0 := by
      intro he
      exact hx (show G t x = 0 by change ψ (q x) * _ = 0; rw [he, zero_mul])
    have hh : x ∈ U := by
      change 0 < ρ x
      by_contra! h
      have he : ρ x = 0 := le_antisymm h (hn x)
      have hq0 : q x = 0 := by simp [q, he]
      exact hb₀ (hq0 ▸ hψ0)
    exact hbound x hh (subset_closure hb₀)
  let V : Set E := {x | x ≠ 0}
  have hZ (x : E) (hx : x ∈ V) (h : x ∉ U) : G 0 =ᶠ[𝓝 x] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hsupp
    have he : ‖x‖ ≤ A * ρ x := hTC 0 hsupp
    have hρ0 : ρ x = 0 := le_antisymm (not_lt.mp h) (hn x)
    rw [hρ0, mul_zero] at he
    exact (norm_pos_iff.mpr hx).not_ge he
  have hGV : ContDiffOn ℝ ∞ (G 0) V := by
    intro x hx
    by_cases h : x ∈ U
    · exact ((hG 0).contDiffAt (hU.mem_nhds h)).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hZ x hx h)).contDiffWithinAt
  have hGscale (r : ℝ) (hr : 0 < r) (x : E) : G 0 (r • x) = G (d * Real.log r) x := by
    have hnorm : q (r • x) = q x := by
      unfold q
      rw [hscale r hr, mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
    change ψ (q (r • x)) * f.val (0 + d * Real.log (ρ (r • x))) =
      ψ (q x) * f.val (d * Real.log r + d * Real.log (ρ x))
    rw [hnorm, hscale r hr, zero_add]
    by_cases hx : ρ x = 0
    · have he : q x = 0 := by simp [q, hx]
      rw [he, hψ0, zero_mul, zero_mul]
    · rw [Real.log_mul hr.ne' hx, mul_add]
  have hdecay (j : ℕ) (a : ℝ) (ha : 0 < a) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ∈ U → q x ∈ K →
        ρ x ^ j * ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C * Real.exp (-a * |d * Real.log (ρ x)|) := by
    obtain ⟨D, hD, hDb⟩ := logSchwartz_comp_mul_jet_bound_on_compact hU hψ hK b hb l hl f j a ha
    refine ⟨D, hD, fun x hx hqk ↦ ?_⟩
    have hr : 0 < ρ x := hx
    have hUscale (y : E) : ρ x • y ∈ U ↔ y ∈ U := by
      change 0 < ρ (ρ x • y) ↔ 0 < ρ y
      rw [hscale _ hr]
      exact (mul_pos_iff_of_pos_left hr)
    have he := norm_iteratedFDeriv_comp_pos_smul hU hr hUscale (G 0) (hG 0) (q x) (hK hqk) j
    rw [hrad x hx, show (fun y : E ↦ G 0 (ρ x • y)) = G (d * Real.log (ρ x)) from
      funext (hGscale (ρ x) hr)] at he
    rw [← he]
    exact hDb _ _ hqk
  have hJetZero (j : ℕ) (x : E) (hx : x ∈ V) (h : ¬(x ∈ U ∧ q x ∈ K)) :
      iteratedFDeriv ℝ j (G 0) x = 0 := by
    have he : G 0 =ᶠ[𝓝 x] 0 := by
      by_cases hux : x ∈ U
      · have hqk : q x ∉ K := fun hqk ↦ h ⟨hux, hqk⟩
        have hqc := (hq.contDiffAt (hU.mem_nhds hux)).continuousAt
        have hKclosed : IsClosed K := isClosed_tsupport ψ
        have hnear : ∀ᶠ y in 𝓝 x, q y ∈ Kᶜ :=
          hqc (hKclosed.isOpen_compl.mem_nhds hqk)
        filter_upwards [hnear] with y hy
        change ψ (q y) * _ = 0
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      · exact hZ x hx hux
    simpa only [iteratedFDeriv_zero, Pi.zero_apply] using (he.iteratedFDeriv ℝ j).eq_of_nhds
  obtain ⟨Q, hQ, hQb⟩ := continuous_homogeneous_radius_le ρ hρ hscale
  have hsmall (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C * ‖x‖ ^ 2 := by
    obtain ⟨C, hC, hCb⟩ := hdecay j ((j + 2 : ℕ) / d) (by positivity)
    refine ⟨C * Q^2, by positivity, fun x hx _ ↦ ?_⟩
    by_cases h : x ∈ U ∧ q x ∈ K
    · have hr : 0 < ρ x := h.1
      have hh := (hCb x h.1 h.2).trans (mul_le_mul_of_nonneg_left
        (exp_log_decay_two_bounds (ρ x) d hr hd (j+2)).1 hC)
      have hJ : ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C * ρ x^2 := by
        apply (mul_le_mul_iff_of_pos_left (pow_pos hr j)).mp
        simpa only [pow_add, mul_left_comm] using hh
      refine hJ.trans ?_
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hn x) (hQb x) 2) hC
    · rw [hJetZero j x hx h, norm_zero]
      positivity
  have hExt (j : ℕ) : ∃ C ≥ 0, ∀ x : E, (ContinuousLinearMap.id ℝ E) x ≠ 0 →
      ‖(ContinuousLinearMap.id ℝ E) x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C * ‖(ContinuousLinearMap.id ℝ E) x‖ ^ 2 := hsmall j
  obtain ⟨hSmooth, hJets⟩ := smooth_flat_zeroExtend_of_jet_bounds (ContinuousLinearMap.id ℝ E) (G 0) hGV hExt
  have hFun : V.indicator (G 0) = G 0 := by
    funext x
    by_cases hx : x = 0
    · subst x
      rw [indicator_of_notMem (show (0 : E) ∉ V from not_not_intro rfl)]
      simp [G, b, q, hψ0]
    · exact indicator_of_mem hx _
  have hsmooth : ContDiff ℝ ∞ (G 0) := hFun ▸ hSmooth
  have hflat (x : E) (hx : ρ x = 0) (j : ℕ) : iteratedFDeriv ℝ j (G 0) x = 0 := by
    by_cases hx0 : x = 0
    · have hj := congrFun (hJets j) x
      change iteratedFDeriv ℝ j (V.indicator (G 0)) x =
        V.indicator (iteratedFDeriv ℝ j (G 0)) x at hj
      rwa [hFun, indicator_of_notMem (show x ∉ V from not_not_intro hx0)] at hj
    · exact hJetZero j x hx0 (fun h ↦ (show 0 < ρ x from h.1).ne' hx)
  let w : 𝓢(E, ℂ) := ⟨G 0, hsmooth, by
    intro k j
    let m := j + k + 2
    obtain ⟨C, hC, hc⟩ := hdecay j ((m : ℝ)/d) (by dsimp [m]; positivity)
    refine ⟨C * A^k, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · rw [hflat x (hx ▸ h0), norm_zero, mul_zero]
      positivity
    by_cases h : x ∈ U ∧ q x ∈ K
    · let r := ρ x
      have hr : 0 < r := h.1
      have hE := exp_log_decay_two_bounds r d hr hd m
      have hBase := hc x h.1 h.2
      have hNorm := hbound x h.1 h.2
      have hJ : r^k * ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C := by
        rcases le_total r 1 with h₁ | h₁
        · have hT := hBase.trans (mul_le_mul_of_nonneg_left hE.1 hC)
          have hJ' : ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C * r^(k+2) := by
            apply (mul_le_mul_iff_of_pos_left (pow_pos hr j)).mp
            simpa only [show m = j+(k+2) by dsimp [m]; omega, pow_add, mul_left_comm] using hT
          have hle : ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C :=
            hJ'.trans (mul_le_of_le_one_right hC (pow_le_one₀ hr.le h₁))
          exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr.le h₁)).trans hle
        · have hT := hBase.trans (mul_le_mul_of_nonneg_left hE.2 hC)
          have hT' : ‖iteratedFDeriv ℝ j (G 0) x‖ ≤ C * (r^m)⁻¹ :=
            (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ h₁)).trans hT
          calc
            _ ≤ r^k * (C * (r^m)⁻¹) := mul_le_mul_of_nonneg_left hT' (by positivity)
            _ = C * (r^k / r^m) := by ring
            _ ≤ C := mul_le_of_le_one_right hC ((div_le_one (pow_pos hr _)).mpr
              (pow_le_pow_right₀ h₁ (by dsimp [m]; omega)))
      calc
        _ ≤ (A*r)^k * ‖iteratedFDeriv ℝ j (G 0) x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hNorm _) (norm_nonneg _)
        _ ≤ A^k * C := by rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left hJ (by positivity)
        _ = C * A^k := mul_comm _ _
    · rw [hJetZero j x hx h, norm_zero, mul_zero]
      positivity⟩
  refine ⟨w, (mem_schwartzFlatSubspace _ _).mpr hflat, fun x ↦ ?_⟩
  change ψ (q x) * f.val (0 + l x) = _
  rw [zero_add]

end

end Masullo
