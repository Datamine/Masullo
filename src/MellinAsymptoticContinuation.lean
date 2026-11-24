-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The converse in Theorem B.2.1.7. Adapted from the Apache-2.0
RiemannMasullo project at commit 56ee28e. See External/PROVENANCE.md. -/

open Filter Function MeasureTheory Set
open scoped Asymptotics ContDiff ENNReal SchwartzMap Topology

namespace Masullo

noncomputable section

set_option quotPrecheck false in
local notation "stripWithTop" =>
  (fun (a : ℝ) (b : WithTop ℝ) ↦ {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
local notation "logWeight" =>
  (fun (σ x : ℝ) ↦ (Real.exp (σ * x) : ℂ))

/-- An exponential growth bound becomes a real-power bound after composition with `log`. -/
private theorem isBigO_comp_log_rpow_of_isBigO_exp {g : ℝ → ℂ} {c : ℝ} {l L : Filter ℝ}
    (h : g =O[l] (fun x ↦ Real.exp (c * x)))
    (ht : Tendsto Real.log L l) (hpos : ∀ᶠ t in L, 0 < t) :
    (fun t ↦ g (Real.log t)) =O[L] (fun t ↦ t ^ c) := by
  apply (h.comp_tendsto ht).congr' EventuallyEq.rfl
  filter_upwards [hpos] with t ht
  simp only [Function.comp_apply, Real.rpow_def_of_pos ht, mul_comm]

section AsymptoticMellin

open Complex

private def cpowLog (a : ℂ) (n : ℕ) : ℝ → ℂ :=
  fun t => (t : ℂ) ^ a * (Real.log t : ℂ) ^ n

private def cpowLogInd (a : ℂ) (n : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (cpowLog a n)

private theorem continuousOn_cpowLog (a : ℂ) (n : ℕ) :
    ContinuousOn (cpowLog a n) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ?_
  · intro t ht
    exact (continuousAt_ofReal_cpow_const t a (Or.inr ht.ne')).continuousWithinAt
  · refine ContinuousOn.pow ?_ _
    exact continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => ht.ne')

private theorem isBigO_cpowLog_nhdsGT (a : ℂ) (n : ℕ) {b : ℝ} (hb : -a.re < b) :
    cpowLog a n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hlim : Tendsto (fun t : ℝ => |Real.log t| ^ (n : ℝ) * t ^ (a.re + b)) (𝓝[>] 0) (𝓝 0) := by
    have hs : -(a.re + b) < 0 := by linarith
    refine (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n : ℝ) hs).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [div_eq_mul_inv, Real.rpow_neg ht.le, inv_inv]
  have hratio : (fun t : ℝ => ‖cpowLog a n t‖ / t ^ (-b)) =ᶠ[𝓝[>] 0]
      fun t => |Real.log t| ^ (n : ℝ) * t ^ (a.re + b) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [cpowLog, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_pow, norm_real,
      Real.norm_eq_abs]
    rw [div_eq_mul_inv, ← Real.rpow_natCast |Real.log t| n, Real.rpow_neg ht.le, inv_inv,
      mul_right_comm, ← Real.rpow_add ht]
    ac_rfl
  have hlim' := hlim.congr' hratio.symm
  filter_upwards [hlim'.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with t ht (hpos : 0 < t)
  have hden : 0 < t ^ (-b) := Real.rpow_pos_of_pos hpos _
  have hlt : ‖cpowLog a n t‖ / t ^ (-b) < 1 := ht
  rw [div_lt_one hden] at hlt
  have hnorm : ‖(t : ℝ) ^ (-b)‖ = t ^ (-b) :=
    Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)
  simpa [hnorm, one_mul] using hlt.le

private theorem isBigO_cpowLogInd_nhdsGT (a : ℂ) (n : ℕ) {b : ℝ} (hb : -a.re < b) :
    cpowLogInd a n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  have hEq : cpowLogInd a n =ᶠ[𝓝[>] (0 : ℝ)] cpowLog a n := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    simp [cpowLogInd, indicator_of_mem ht']
  exact (isBigO_cpowLog_nhdsGT a n hb).congr' hEq.symm .rfl

private theorem isBigO_cpowLogInd_atTop (a : ℂ) (n : ℕ) (c : ℝ) :
    cpowLogInd a n =O[atTop] (fun t : ℝ => t ^ c) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hnot : t ∉ Ioc (0 : ℝ) 1 := fun h => lt_irrefl (1 : ℝ) (ht.trans_le h.2)
  simp [cpowLogInd, indicator_of_notMem hnot]

private theorem locallyIntegrableOn_indicator_Ioc {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) :
    LocallyIntegrableOn ((Ioc (0 : ℝ) 1).indicator g) (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨Ioo (x / 2) (x + 1), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
    ?_⟩
  have hIcc : Icc (x / 2) (x + 1) ⊆ Ioi 0 := by
    intro t ht
    exact lt_of_lt_of_le (half_pos hx0) ht.1
  have hgcont : ContinuousOn g (Icc (x / 2) (x + 1)) := hg.mono hIcc
  have hint : IntegrableOn g (Icc (x / 2) (x + 1)) :=
    hgcont.integrableOn_compact isCompact_Icc
  have hsub : Ioc (0 : ℝ) 1 ∩ Ioo (x / 2) (x + 1) ⊆ Icc (x / 2) (x + 1) := by
    intro t ht
    exact ⟨le_of_lt ht.2.1, le_of_lt ht.2.2⟩
  simpa using (integrableOn_indicator_iff measurableSet_Ioc).2 (hint.mono_set hsub)

private theorem locallyIntegrableOn_cpowLogInd (a : ℂ) (n : ℕ) :
    LocallyIntegrableOn (cpowLogInd a n) (Ioi 0) :=
  locallyIntegrableOn_indicator_Ioc (continuousOn_cpowLog a n)

private theorem log_mul_cpowLogInd (a : ℂ) (n : ℕ) :
    (fun t : ℝ => (Real.log t : ℂ) * cpowLogInd a n t) = cpowLogInd a (n + 1) := by
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [cpowLogInd, indicator_of_mem ht, cpowLog]
    calc
      (Real.log t : ℂ) * ((t : ℂ) ^ a * (Real.log t : ℂ) ^ n)
          = (t : ℂ) ^ a * ((Real.log t : ℂ) * (Real.log t : ℂ) ^ n) := by ring
      _ = (t : ℂ) ^ a * (Real.log t : ℂ) ^ (n + 1) := by rw [← pow_succ']
  · simp [cpowLogInd, indicator_of_notMem ht]

private theorem hasMellin_cpowLogInd (a : ℂ) (n : ℕ) {s : ℂ} (hs : 0 < s.re + a.re) :
    HasMellin (cpowLogInd a n) s
      ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s + a) ^ (-(n : ℤ) - 1)) := by
  have hhalf : IsOpen {z : ℂ | 0 < z.re + a.re} := by
    have hEq : {z : ℂ | 0 < z.re + a.re} = (fun z : ℂ => z.re + a.re) ⁻¹' Ioi 0 := by
      ext z; rfl
    rw [hEq]
    exact isOpen_Ioi.preimage (continuous_re.add continuous_const)
  have key : ∀ n : ℕ, ∀ s : ℂ, 0 < s.re + a.re →
      HasMellin (cpowLogInd a n) s (iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h0 := hasMellin_cpow_Ioc a hs
      have hfun : cpowLogInd a 0 = (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ a) := by
        funext t
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · rw [cpowLogInd, indicator_of_mem ht, indicator_of_mem ht, cpowLog, pow_zero, mul_one]
        · rw [cpowLogInd, indicator_of_notMem ht, indicator_of_notMem ht]
      refine ⟨?_, ?_⟩
      · rw [hfun]; exact h0.1
      · rw [hfun, iteratedDeriv_zero, inv_eq_one_div]; exact h0.2
    | succ n ih =>
      intro s hs
      have hloc := locallyIntegrableOn_cpowLogInd a n
      have htop := isBigO_cpowLogInd_atTop a n (-(s.re + 1))
      set b0 : ℝ := (-a.re + s.re) / 2
      have hb0_lt : b0 < s.re := by dsimp [b0]; linarith
      have hb0_gt : -a.re < b0 := by dsimp [b0]; linarith
      have hbot := isBigO_cpowLogInd_nhdsGT a n hb0_gt
      have hder := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := b0)
        hloc htop (by linarith) hbot hb0_lt
      have hsmul := log_mul_cpowLogInd a n
      have hHas : HasDerivAt (mellin (cpowLogInd a n)) (mellin (cpowLogInd a (n + 1)) s) s := by
        simpa [hsmul, real_smul] using hder.2
      have hconv : MellinConvergent (cpowLogInd a (n + 1)) s := by
        simpa [hsmul, real_smul] using hder.1
      have hagree : mellin (cpowLogInd a n) =ᶠ[𝓝 s]
          iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) := by
        filter_upwards [hhalf.mem_nhds hs] with z hz
        exact (ih z hz).2
      refine ⟨hconv, ?_⟩
      rw [← hHas.deriv, hagree.deriv_eq, ← iteratedDeriv_succ]
  have hkey := key n s hs
  have hform : iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) s =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (s + a) ^ (-(n : ℤ) - 1) := by
    rw [iteratedDeriv_eq_iterate]
    have hlin := congr_fun (iter_deriv_inv_linear n (1 : ℂ) a) s
    simpa [show (-1 - (n : ℤ) = -(n : ℤ) - 1) by ring] using hlin
  simpa [hform] using hkey

private theorem hasMellin_finset_sum {ι : Type*} (p : Finset ι) (f : ι → ℝ → ℂ) (v : ι → ℂ)
    (s : ℂ) (h : ∀ i ∈ p, HasMellin (f i) s (v i)) :
    HasMellin (fun t => ∑ i ∈ p, f i t) s (∑ i ∈ p, v i) := by
  classical
  induction p using Finset.induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_empty, MellinConvergent, smul_zero]
      exact integrableOn_zero
    · simp [mellin, Finset.sum_empty]
  | insert i p hi ih =>
    have hfun : (fun t => ∑ j ∈ insert i p, f j t) = fun t => f i t + ∑ j ∈ p, f j t := by
      funext t
      rw [Finset.sum_insert hi]
    have hval : (∑ j ∈ insert i p, v j) = v i + ∑ j ∈ p, v j := Finset.sum_insert hi
    rw [hfun, hval]
    have hi' := h i (Finset.mem_insert_self i p)
    have hp := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have Hadd := hasMellin_add hi'.1 hp.1
    rw [hi'.2, hp.2] at Hadd
    exact Hadd

private theorem exists_lt_withTop {x : ℝ} {b : WithTop ℝ} (hx : (x : WithTop ℝ) < b) :
    ∃ σ : ℝ, x < σ ∧ (σ : WithTop ℝ) < b := by
  cases b with
  | top =>
    exact ⟨x + 1, by linarith, WithTop.coe_lt_top _⟩
  | coe B =>
    have hxB : x < B := by simpa [WithTop.coe_lt_coe] using hx
    refine ⟨(x + B) / 2, by linarith, ?_⟩
    simpa [WithTop.coe_lt_coe] using (by linarith : (x + B) / 2 < B)

private theorem isOpen_reStrip (A : ℝ) (b : WithTop ℝ) :
    IsOpen {s : ℂ | A < s.re ∧ (s.re : WithTop ℝ) < b} := by
  have hset : IsOpen {x : ℝ | A < x ∧ (x : WithTop ℝ) < b} := by
    cases b with
    | top =>
      have hEq : {x : ℝ | A < x ∧ (x : WithTop ℝ) < ⊤} = Ioi A := by
        ext x
        simp [WithTop.coe_lt_top]
      rw [hEq]
      exact isOpen_Ioi
    | coe B =>
      have hEq : {x : ℝ | A < x ∧ (x : WithTop ℝ) < B} = Ioo A B := by
        ext x
        simp [WithTop.coe_lt_coe]
      rw [hEq]
      exact isOpen_Ioo
  convert hset.preimage continuous_re using 1
  ext s
  simp

/-- Paper: Theorem B.2.1.7(2), p. 596. A finite power-log expansion at zero
gives a meromorphic continuation, with poles of the prescribed orders.
Deviation: Meromorphic continuation is in normal form. The coefficients are
indexed by their logarithm degree, starting at zero. -/
theorem exists_meromorphic_mellin_of_asymptoticExpansion
    (a A : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hA : A < 0) (hab : (a : WithTop ℝ) < b)
    (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (hWeighted : ∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
      ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight σ x * φ (Real.exp x))
    (poles : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ α ∈ poles, 1 ≤ m α)
    (hpoles : ∀ α ∈ poles, (-α).re ∈ Ioc A a) (c : ℂ → ℕ → ℂ)
    (hc : ∀ α ∈ poles, c α (m α - 1) ≠ 0)
    (hAsymptotic : (fun t : ℝ ↦ φ t -
      ∑ α ∈ poles, ∑ j ∈ Finset.range (m α), c α j * (t : ℂ) ^ α * (Real.log t : ℂ) ^ j)
      =O[𝓝[>] (0 : ℝ)] fun t ↦ t ^ (-A)) :
    ∃ F : ℂ → ℂ, MeromorphicNFOn F (stripWithTop A b) ∧
      (∀ s ∈ stripWithTop a b, HasMellin φ s (F s)) ∧
      (∀ α ∈ poles, meromorphicOrderAt F (-α) = -((m α : ℕ) : ℤ)) ∧
      ∀ s ∈ stripWithTop A b, -s ∉ poles → 0 ≤ meromorphicOrderAt F s := by
  classical
  -- Cut the power-log expansion off at 1. Its Mellin transform is an explicit
  -- rational function, and the remainder is holomorphic on the wider strip.
  let E : ℝ → ℂ := fun t =>
    ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
      c α j * (t : ℂ) ^ α * (Real.log t : ℂ) ^ j
  let cutoff : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator E
  let ψ : ℝ → ℂ := fun t => φ t - cutoff t
  let coeff (β : ℂ) (j : ℕ) : ℂ :=
    c β j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ)
  let P : ℂ → ℂ := fun z =>
    ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
      coeff α j * (z + α) ^ (-(j : ℤ) - 1)
  let F : ℂ → ℂ := fun z => if -z ∈ poles then 0 else mellin ψ z + P z
  have hEfun : E = ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
      fun t : ℝ => c α j * cpowLog α j t := by
    funext t
    simp only [E, cpowLog, Finset.sum_apply, mul_assoc]
  have hEcont : ContinuousOn E (Ioi 0) := by
    rw [hEfun]
    refine Finset.sum_induction _ (fun g => ContinuousOn g (Ioi 0))
      (fun _ _ hf hg => hf.add hg) continuousOn_const ?_
    intro α _hα
    refine Finset.sum_induction _ (fun g => ContinuousOn g (Ioi 0))
      (fun _ _ hf hg => hf.add hg) continuousOn_const ?_
    intro j _hj
    exact continuousOn_const.mul (continuousOn_cpowLog α j)
  have hψloc : LocallyIntegrableOn ψ (Ioi 0) :=
    (hφ.continuousOn.locallyIntegrableOn measurableSet_Ioi).sub
      (locallyIntegrableOn_indicator_Ioc hEcont)
  have hψφ : ψ =ᶠ[atTop] φ := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    have hnot : t ∉ Ioc (0 : ℝ) 1 := fun h => lt_irrefl (1 : ℝ) (ht.trans_le h.2)
    simp [ψ, cutoff, indicator_of_notMem hnot]
  have hψE : ψ =ᶠ[𝓝[>] (0 : ℝ)] (fun t => φ t - E t) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    simp [ψ, cutoff, indicator_of_mem ht']
  have hφtop : ∀ {σ : ℝ}, a < σ → (σ : WithTop ℝ) < b →
      φ =O[atTop] (fun t : ℝ => t ^ (-σ)) := by
    intro σ hσa hσb
    obtain ⟨g, hg⟩ := hWeighted σ hσa hσb
    have hprof : (fun x : ℝ => φ (Real.exp x)) =O[atTop] (fun x => Real.exp (-σ * x)) := by
      refine Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g) ?_
      filter_upwards with x
      have hmul : φ (Real.exp x) = (Real.exp (-σ * x) : ℂ) * g x := by
        have hne : (Real.exp (σ * x) : ℂ) ≠ 0 := by
          exact_mod_cast Real.exp_ne_zero (σ * x)
        apply mul_left_cancel₀ hne
        calc
          (Real.exp (σ * x) : ℂ) * φ (Real.exp x) = g x := (hg x).symm
          _ = (Real.exp (σ * x) : ℂ) * ((Real.exp (-σ * x) : ℂ) * g x) := by
            rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add]
            have hzero : σ * x + -σ * x = 0 := by ring
            rw [hzero, Real.exp_zero, ofReal_one, one_mul]
      rw [hmul]
      calc
        ‖(Real.exp (-σ * x) : ℂ) * g x‖ = Real.exp (-σ * x) * ‖g x‖ := by
          rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-σ * x) * SchwartzMap.seminorm ℂ 0 0 g :=
          mul_le_mul_of_nonneg_left (g.norm_le_seminorm ℂ x) (Real.exp_nonneg _)
        _ = SchwartzMap.seminorm ℂ 0 0 g * ‖Real.exp (-σ * x)‖ := by
          rw [mul_comm, Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine (isBigO_comp_log_rpow_of_isBigO_exp hprof Real.tendsto_log_atTop
      (eventually_gt_atTop 0)).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Real.exp_log ht]
  have hpow : ∀ {p q : ℝ}, q ≤ p →
      (fun t : ℝ => t ^ p) =O[𝓝[>] (0 : ℝ)] (fun t => t ^ q) := by
    intro p q hpq
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht0 : 0 < t := ht.1
    have hle1 : t ≤ 1 := ht.2.le
    have hcmp : t ^ p ≤ t ^ q := by
      have happ : p = q + (p - q) := by ring
      rw [happ, Real.rpow_add ht0]
      have hsmall : t ^ (p - q) ≤ 1 := Real.rpow_le_one ht0.le hle1 (by linarith)
      calc
        t ^ q * t ^ (p - q) ≤ t ^ q * 1 :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg ht0.le _)
        _ = t ^ q := mul_one _
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), one_mul] using hcmp
  have hψbot : ∀ {s : ℂ}, A < s.re →
      ψ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-((A + s.re) / 2))) := by
    intro s hsA
    have hrem := hAsymptotic.trans
      (hpow (p := -A) (q := -((A + s.re) / 2)) (by linarith))
    exact hrem.congr' hψE.symm .rfl
  have hψdecay : ∀ s : ℂ, A < s.re → (s.re : WithTop ℝ) < b →
      ∃ σ : ℝ, s.re < σ ∧ ψ =O[atTop] (fun t : ℝ => t ^ (-σ)) ∧
        ψ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-((A + s.re) / 2))) ∧
        (A + s.re) / 2 < s.re := by
    intro s hsA hsb
    have hx : ((max a s.re : ℝ) : WithTop ℝ) < b := by
      by_cases hsa : s.re ≤ a
      · rw [max_eq_left hsa]; exact hab
      · rw [max_eq_right (le_of_not_ge hsa)]; exact hsb
    obtain ⟨σ, hσgt, hσb⟩ := exists_lt_withTop hx
    have hσa : a < σ := lt_of_le_of_lt (le_max_left a s.re) hσgt
    have hσs : s.re < σ := lt_of_le_of_lt (le_max_right a s.re) hσgt
    refine ⟨σ, hσs, (hφtop hσa hσb).congr' hψφ.symm .rfl, hψbot hsA, by linarith⟩
  have hstrip : IsOpen (stripWithTop A b) := isOpen_reStrip A b
  have hHdiff : DifferentiableOn ℂ (mellin ψ) (stripWithTop A b) := by
    intro s hs
    obtain ⟨σ, hσs, htop, hbot, hb0⟩ := hψdecay s hs.1 hs.2
    exact (mellin_differentiableAt_of_isBigO_rpow hψloc htop hσs hbot hb0).differentiableWithinAt
  have hHanal : ∀ s ∈ stripWithTop A b, AnalyticAt ℂ (mellin ψ) s :=
    fun s hs => hHdiff.analyticAt (hstrip.mem_nhds hs)
  have hterm : ∀ β ∈ poles, ∀ j ∈ Finset.range (m β), ∀ s : ℂ, a < s.re →
      HasMellin ((Ioc (0 : ℝ) 1).indicator
        (fun t => c β j * (t : ℂ) ^ β * (Real.log t : ℂ) ^ j)) s
        (coeff β j * (s + β) ^ (-(j : ℤ) - 1)) := by
    intro β hβ j _hj s hs
    have hre : 0 < s.re + β.re := by
      have : -β.re ≤ a := by simpa [neg_re] using (hpoles β hβ).2
      linarith
    have hbase := hasMellin_cpowLogInd β j hre
    have hsm := hasMellin_const_smul hbase.1 (c β j)
    rw [hbase.2] at hsm
    have hfun : (fun t => (c β j) • cpowLogInd β j t) =
        (Ioc (0 : ℝ) 1).indicator
          (fun t => c β j * (t : ℂ) ^ β * (Real.log t : ℂ) ^ j) := by
      funext t
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · simp [cpowLogInd, cpowLog, ht, indicator_of_mem, smul_eq_mul, mul_assoc]
      · simp [cpowLogInd, ht, indicator_of_notMem, smul_eq_mul]
    have hval : (c β j) • ((-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
        (s + β) ^ (-(j : ℤ) - 1)) = coeff β j * (s + β) ^ (-(j : ℤ) - 1) := by
      simp [coeff, smul_eq_mul, mul_assoc]
    rw [hfun, hval] at hsm
    exact hsm
  have hcutFun : cutoff = fun t =>
      ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
        (Ioc (0 : ℝ) 1).indicator
          (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp [cutoff, E, indicator_of_mem ht]
    · simp [cutoff, E, indicator_of_notMem ht]
  have hcut : ∀ s : ℂ, a < s.re → HasMellin cutoff s (P s) := by
    intro s hs
    have hsum := hasMellin_finset_sum poles
      (fun α t => ∑ j ∈ Finset.range (m α),
        (Ioc (0 : ℝ) 1).indicator
          (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t)
      (fun α => ∑ j ∈ Finset.range (m α), coeff α j * (s + α) ^ (-(j : ℤ) - 1)) s
      ?_
    · rw [hcutFun]
      simpa [P, Finset.sum_apply] using hsum
    · intro α hα
      refine hasMellin_finset_sum (Finset.range (m α))
        (fun j t => (Ioc (0 : ℝ) 1).indicator
          (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t)
        (fun j => coeff α j * (s + α) ^ (-(j : ℤ) - 1)) s ?_
      intro j hj
      simpa using hterm α hα j hj s hs
  have hsplit : ∀ s : ℂ, s ∈ stripWithTop a b → HasMellin φ s (mellin ψ s + P s) := by
    intro s hs
    obtain ⟨σ, hσs, hσb⟩ := exists_lt_withTop hs.2
    have htop : ψ =O[atTop] (fun t => t ^ (-σ)) :=
      (hφtop (hs.1.trans hσs) hσb).congr' hψφ.symm .rfl
    have hbot : ψ =O[𝓝[>] 0] (fun t => t ^ (-((A + s.re) / 2))) :=
      hψbot (lt_trans hA (lt_trans ha hs.1))
    have hψc : MellinConvergent ψ s :=
      mellinConvergent_of_isBigO_rpow hψloc htop hσs hbot (by linarith [hs.1, hA, ha])
    have hcu := hcut s hs.1
    have Hadd := hasMellin_add hψc hcu.1
    have hsum : (fun t => ψ t + cutoff t) = φ := by
      funext t; simp [ψ]
    rw [hsum, hcu.2] at Hadd
    exact Hadd
  have hPanal : ∀ {s : ℂ}, -s ∉ poles → AnalyticAt ℂ P s := by
    intro s hs
    have hPfun : P = ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
        fun z : ℂ => coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
      funext z
      simp [P, Finset.sum_apply]
    rw [hPfun]
    refine Finset.sum_induction _ (fun g => AnalyticAt ℂ g s)
      (fun _ _ hf hg => hf.add hg) analyticAt_const ?_
    intro α hα
    refine Finset.sum_induction _ (fun g => AnalyticAt ℂ g s)
      (fun _ _ hf hg => hf.add hg) analyticAt_const ?_
    intro j _hj
    refine analyticAt_const.mul ?_
    have hne : s + α ≠ 0 := by
      intro hzero
      apply hs
      have : s = -α := add_eq_zero_iff_eq_neg.mp hzero
      simpa [this] using hα
    exact ((analyticAt_id.add analyticAt_const).zpow hne)
  have hpoleClosed : IsClosed {z : ℂ | -z ∈ poles} := by
    have hEq : {z : ℂ | -z ∈ poles} = Neg.neg '' (poles : Set ℂ) := by
      ext z
      constructor
      · intro hz
        refine ⟨-z, by simpa using hz, by simp⟩
      · rintro ⟨α, hα, rfl⟩
        simpa using hα
    rw [hEq]
    exact (poles.finite_toSet.image Neg.neg).isClosed
  have hdecomp : ∀ α ∈ poles, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (-α) ∧ G (-α) ≠ 0 ∧
      F =ᶠ[𝓝 (-α)] fun z => (z - (-α)) ^ (-(m α : ℤ)) • G z := by
    intro α hα
    have hk : (1 : ℕ) ≤ m α := hm α hα
    let x : ℂ := -α
    have hxstrip : x ∈ stripWithTop A b := by
      have hI := hpoles α hα
      refine ⟨by simpa [x, neg_re] using hI.1, ?_⟩
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by simpa [x, neg_re] using hI.2)) hab
    let regular : ℂ → ℂ := fun z =>
      mellin ψ z + ∑ β ∈ poles.erase α, ∑ j ∈ Finset.range (m β),
        coeff β j * (z + β) ^ (-(j : ℤ) - 1)
    let singular : ℂ → ℂ := fun z =>
      ∑ j ∈ Finset.range (m α),
        c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) * (z + α) ^ (m α - (j + 1))
    let G : ℂ → ℂ := fun z => (z + α) ^ (m α) * regular z + singular z
    have hreg : AnalyticAt ℂ regular x := by
      have hfun : regular = (fun z : ℂ => mellin ψ z) +
          ∑ β ∈ poles.erase α, ∑ j ∈ Finset.range (m β),
            fun z : ℂ => coeff β j * (z + β) ^ (-(j : ℤ) - 1) := by
        funext z
        simp [regular, Finset.sum_apply]
      rw [hfun]
      refine (hHanal x hxstrip).add ?_
      refine Finset.analyticAt_sum (poles.erase α) ?_
      intro β hβ
      have hβne : β ≠ α := (Finset.mem_erase.mp hβ).1
      refine Finset.analyticAt_sum (Finset.range (m β)) ?_
      intro j _hj
      refine analyticAt_const.mul ?_
      have hne : x + β ≠ 0 := by
        intro hzero
        apply hβne
        have h' : β + (-α) = 0 := by simpa [x, add_comm] using hzero
        exact (add_eq_zero_iff_eq_neg.mp h').trans (neg_neg α)
      exact ((analyticAt_id.add analyticAt_const).zpow hne)
    have hsingA : AnalyticAt ℂ singular x := by
      have hfun : singular = ∑ j ∈ Finset.range (m α),
          fun z : ℂ => c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
            (z + α) ^ (m α - (j + 1)) := by
        funext z
        simp [singular, Finset.sum_apply]
      rw [hfun]
      refine Finset.analyticAt_sum (Finset.range (m α)) ?_
      intro j _hj
      exact analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow _)
    have hGanal : AnalyticAt ℂ G x :=
      (((analyticAt_id.add analyticAt_const).pow (m α)).mul hreg).add hsingA
    have hsingx : singular x = coeff α (m α - 1) := by
      have hmemj : m α - 1 ∈ Finset.range (m α) :=
        Finset.mem_range.mpr (Nat.sub_lt (Nat.lt_of_lt_of_le zero_lt_one hk) zero_lt_one)
      rw [show singular x = ∑ j ∈ Finset.range (m α),
          c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
            (x + α) ^ (m α - (j + 1)) from rfl]
      rw [Finset.sum_eq_single_of_mem (m α - 1) hmemj]
      · rw [show m α - (m α - 1 + 1) = 0 by rw [Nat.sub_add_cancel hk, Nat.sub_self],
          pow_zero, mul_one]
      · intro j hj hjne
        have hjk : j < m α := Finset.mem_range.mp hj
        have hjl : j ≤ m α - 1 := Nat.le_sub_one_of_lt hjk
        have hjs : j < m α - 1 := lt_of_le_of_ne hjl hjne
        have hsucc : j + 1 < m α := by
          have hcancel : (m α - 1) + 1 = m α := Nat.sub_add_cancel hk
          simpa [hcancel] using Nat.add_lt_add_right hjs 1
        rw [show x + α = 0 by simp [x], zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hsucc)),
          mul_zero]
    have hGne : G x ≠ 0 := by
      have hzero : (x + α) ^ (m α) * regular x = 0 := by
        simp [x, zero_pow (Nat.one_le_iff_ne_zero.mp hk)]
      rw [show G x = (x + α) ^ (m α) * regular x + singular x from rfl, hzero, zero_add, hsingx]
      unfold coeff
      apply mul_ne_zero
      · apply mul_ne_zero
        · simpa using hc α hα
        · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      · exact_mod_cast (Nat.factorial_pos (m α - 1)).ne'
    have hiden : ∀ z, z ≠ x →
        mellin ψ z + P z = (z - x) ^ (-(m α : ℤ)) * G z := by
      intro z hz
      have hzα : z + α ≠ 0 := by
        intro hzero
        exact hz ((add_eq_zero_iff_eq_neg.mp hzero).trans (by simp [x]))
      have hshift : z - x = z + α := by simp [x]
      have hcancel : (z + α) ^ (-(m α : ℤ)) * ((z + α) ^ (m α) * regular z) = regular z := by
        have hmul : (z + α) ^ (-(m α : ℤ)) * (z + α) ^ ((m α : ℕ) : ℤ) = 1 := by
          rw [← zpow_add₀ hzα, neg_add_cancel, zpow_zero]
        calc
          (z + α) ^ (-(m α : ℤ)) * ((z + α) ^ (m α) * regular z)
              = ((z + α) ^ (-(m α : ℤ)) * (z + α) ^ ((m α : ℕ) : ℤ)) * regular z := by
                rw [← mul_assoc, ← zpow_natCast]
          _ = regular z := by rw [hmul, one_mul]
      have hsingmul : (z + α) ^ (-(m α : ℤ)) * singular z =
          ∑ j ∈ Finset.range (m α), coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
        simp only [singular, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hle : j + 1 ≤ m α := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        have hexp : (z + α) ^ (-(m α : ℤ)) * (z + α) ^ (m α - (j + 1)) =
            (z + α) ^ (-(j : ℤ) - 1) := by
          rw [← zpow_natCast, ← zpow_add₀ hzα]
          congr 1
          rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
          ring
        calc
          (z + α) ^ (-(m α : ℤ)) *
              (c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
                (z + α) ^ (m α - (j + 1)))
            = c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
                ((z + α) ^ (-(m α : ℤ)) * (z + α) ^ (m α - (j + 1))) := by ring
          _ = coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by rw [hexp]
      have hsplitP : P z =
          (∑ β ∈ poles.erase α, ∑ j ∈ Finset.range (m β),
            coeff β j * (z + β) ^ (-(j : ℤ) - 1)) +
          ∑ j ∈ Finset.range (m α), coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
        have hsum := Finset.sum_erase_add
          (f := fun β => ∑ j ∈ Finset.range (m β),
            coeff β j * (z + β) ^ (-(j : ℤ) - 1)) (s := poles) hα
        simpa [P, add_comm] using hsum.symm
      calc
        mellin ψ z + P z
            = regular z + ∑ j ∈ Finset.range (m α),
                coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
              simp only [regular, hsplitP, add_assoc]
        _ = regular z + (z + α) ^ (-(m α : ℤ)) * singular z := by rw [← hsingmul]
        _ = (z + α) ^ (-(m α : ℤ)) * ((z + α) ^ (m α) * regular z) +
              (z + α) ^ (-(m α : ℤ)) * singular z := by rw [hcancel]
        _ = (z - x) ^ (-(m α : ℤ)) * G z := by rw [← mul_add, hshift]
    let bad : Finset ℂ := (poles.erase α).image fun β => -β
    have hxbad : x ∉ (bad : Set ℂ) := by
      intro hx
      obtain ⟨β, hβ, hβx⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_erase.mp hβ).1 (by simpa [x] using hβx)
    have havoid : {z : ℂ | z ∉ (bad : Set ℂ)} ∈ 𝓝 x :=
      (isOpen_compl_iff.mpr bad.finite_toSet.isClosed).mem_nhds hxbad
    have hEq : F =ᶠ[𝓝 x] fun z => (z - x) ^ (-(m α : ℤ)) • G z := by
      filter_upwards [havoid] with z hz
      by_cases hzx : z = x
      · subst hzx
        have hk0 : (-(m α : ℤ)) ≠ 0 := by
          intro hk0
          exact Nat.one_le_iff_ne_zero.mp hk (by exact_mod_cast neg_eq_zero.mp hk0)
        rw [sub_self, zero_zpow (-(m α : ℤ)) hk0, zero_smul]
        simp [F, x, hα]
      · have hnot : -z ∉ poles := by
          intro hzmem
          by_cases hαeq : -z = α
          · exact hzx (by simpa [x] using neg_eq_iff_eq_neg.mp hαeq)
          · exact hz (Finset.mem_image.mpr ⟨-z, Finset.mem_erase.mpr ⟨hαeq, hzmem⟩, by simp⟩)
        simp [F, hnot, smul_eq_mul, hiden z hzx]
    exact ⟨G, hGanal, hGne, hEq⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hmem : -s ∈ poles
    · obtain ⟨α, hα, hsα⟩ : ∃ α ∈ poles, s = -α := ⟨-s, hmem, by simp⟩
      obtain ⟨G, hGan, hGne, hEq⟩ := hdecomp α hα
      rw [hsα]
      exact Or.inr ⟨(-(m α : ℤ)), G, hGan, hGne, hEq⟩
    · have hFeq : F =ᶠ[𝓝 s] fun z => mellin ψ z + P z := by
        filter_upwards [(isOpen_compl_iff.mpr hpoleClosed).mem_nhds (by simpa using hmem)] with z hz
        simp [F, show -z ∉ poles from by simpa using hz]
      exact (((hHanal s hs).add (hPanal hmem)).congr hFeq.symm).meromorphicNFAt
  · intro s hs
    have hnot : -s ∉ poles := by
      intro hmem
      have : s.re ≤ a := by simpa [neg_neg, neg_re] using (hpoles (-s) hmem).2
      exact (not_lt_of_ge this) hs.1
    simpa [F, hnot] using hsplit s hs
  · intro α hα
    obtain ⟨G, hGan, hGne, hEq⟩ := hdecomp α hα
    have hNF : MeromorphicNFAt F (-α) := Or.inr ⟨(-(m α : ℤ)), G, hGan, hGne, hEq⟩
    have hcast : (((-(m α : ℤ)) : ℤ) : WithTop ℤ) = -((m α : ℕ) : ℤ) := by
      simp
    rw [← hcast, meromorphicOrderAt_eq_int_iff hNF.meromorphicAt]
    exact ⟨G, hGan, hGne, hEq.filter_mono nhdsWithin_le_nhds⟩
  · intro s hs hnot
    have hFeq : F =ᶠ[𝓝 s] fun z => mellin ψ z + P z := by
      filter_upwards [(isOpen_compl_iff.mpr hpoleClosed).mem_nhds (by simpa using hnot)] with z hz
      simp [F, show -z ∉ poles from by simpa using hz]
    exact (((hHanal s hs).add (hPanal hnot)).congr hFeq.symm).meromorphicOrderAt_nonneg

/-- The inverse Mellin error is bounded by the vertical line's (L^1) norm
times the modulus raised to the negative abscissa. -/
theorem mellinInv_norm_le_verticalIntegral (σ : ℝ) (F : ℂ → ℂ)
    {t : ℝ} (ht : 0 < t) :
    ‖mellinInv σ F t‖ ≤
      ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖) * t ^ (-σ) := by
  let v (y : ℝ) : ℂ := (σ : ℂ) + y * I
  have hnorm (y : ℝ) : ‖(t : ℂ) ^ (-v y) • F (v y)‖ = t ^ (-σ) * ‖F (v y)‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp [v, neg_re, add_re, mul_re]
  change ‖(1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, (t : ℂ) ^ (-v y) • F (v y))‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖(t : ℂ) ^ (-v y) • F (v y)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖F (v y)‖) * t ^ (-σ) := by
      simp_rw [hnorm, integral_const_mul]
      ring

/-- The shifted inverse Mellin integral has the required size for the error
term in B.2.1.7(1) once the contour has been shifted to the pole-free line. -/
theorem mellinInv_isBigO_nhdsGT_zero (σ : ℝ) (F : ℂ → ℂ) :
    mellinInv σ F =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-σ) := by
  refine Asymptotics.IsBigO.of_bound
    ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact mellinInv_norm_le_verticalIntegral σ F ht

end AsymptoticMellin

end

end Masullo
