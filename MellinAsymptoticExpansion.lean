import MellinAsymptoticContinuation
import MellinStrip
import RectangleResidue

open Complex Filter MeasureTheory Set
open scoped Asymptotics ContDiff Interval Topology

namespace Masullo

noncomputable section

private def verticalMellinPoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp]
private theorem verticalMellinPoint_re (x y : ℝ) : (verticalMellinPoint x y).re = x := by
  simp [verticalMellinPoint, mul_re]

@[simp]
private theorem verticalMellinPoint_im (x y : ℝ) : (verticalMellinPoint x y).im = y := by
  simp [verticalMellinPoint, mul_im]

/-- The entire kernel for inverse Mellin integration, equal to `t ^ (-z)` for `t > 0`. -/
def inverseMellinFactor (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.log t : ℂ) * z)

private theorem inverseMellinFactor_eq {t : ℝ} (ht : 0 < t) (z : ℂ) :
    inverseMellinFactor t z = (t : ℂ) ^ (-z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ← Complex.ofReal_log ht.le, inverseMellinFactor]
  congr 1
  ring

private theorem inverseMellinFactor_analytic (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (inverseMellinFactor t) z := by
  unfold inverseMellinFactor
  fun_prop

/-- The inverse Mellin residue in terms of the Taylor coefficients of an
analytic factor obtained by clearing a pole of order `n+1`. -/
theorem meromorphicResidue_inverseMellin_of_cleared {F g : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g p) (hne : g p ≠ 0)
    (he : F =ᶠ[𝓝[≠] p] fun z ↦ (z - p) ^ (-((n : ℤ) + 1)) • g z)
    {t : ℝ} (ht : 0 < t) :
    meromorphicResidue (inverseMellinFactor t * F) p =
      ∑ k ∈ Finset.range (n + 1),
        (iteratedDeriv (n - k) g p / ((n - k).factorial : ℂ)) *
          ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * (t : ℂ) ^ (-p) * (Real.log t : ℂ) ^ k := by
  let Φ := inverseMellinFactor t
  let d : ℂ := -(Real.log t : ℂ)
  have hΦ := inverseMellinFactor_analytic t p
  have hprod : AnalyticAt ℂ (Φ * g) p := hΦ.mul hg
  have hprod_ne : (Φ * g) p ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hne
  have hEq : Φ * F =ᶠ[𝓝[≠] p] fun z ↦ (Φ * g) z / (z - p) ^ (n + 1) := by
    filter_upwards [he] with z hz
    change Φ z * F z = (Φ z * g z) / (z - p) ^ (n + 1)
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hz, hn, zpow_neg, zpow_natCast, smul_eq_mul, div_eq_mul_inv]
    ring
  have hDeriv (k : ℕ) : iteratedDeriv k Φ p = d ^ k * Φ p :=
    congrFun (iteratedDeriv_cexp_const_mul k d) p
  rw [meromorphicResidue_congr hEq, meromorphicResidue_div_sub_pow n hprod hprod_ne,
    iteratedDeriv_mul hΦ.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfact (j : ℕ) : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hchoose : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [hDeriv, show Φ p = (t : ℂ) ^ (-p) from inverseMellinFactor_eq ht p,
    show d ^ k = (-1 : ℂ) ^ k * (Real.log t : ℂ) ^ k from neg_pow _ _, ← hchoose]
  have hcn : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  field_simp [hfact k, hfact (n-k), hcn]
  <;> ring

/-- At a pole of order `n+1`, multiplication by the inverse Mellin factor
produces a power times a logarithmic polynomial of exact degree `n`. -/
theorem meromorphicResidue_inverseMellin_powerLog {F : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hF : MeromorphicAt F p) (horder : meromorphicOrderAt F p = (-((n : ℤ) + 1) : ℤ)) :
    ∃ c : ℕ → ℂ, c n ≠ 0 ∧ ∀ t : ℝ, 0 < t →
      meromorphicResidue (inverseMellinFactor t * F) p =
        ∑ k ∈ Finset.range (n + 1), c k * (t : ℂ) ^ (-p) * (Real.log t : ℂ) ^ k := by
  obtain ⟨g, hg, hne, he⟩ := (meromorphicOrderAt_eq_int_iff hF).mp horder
  let c (k : ℕ) : ℂ := (iteratedDeriv (n-k) g p / ((n-k).factorial : ℂ)) *
    ((-1 : ℂ) ^ k / (k.factorial : ℂ))
  refine ⟨c, ?_, fun t ht ↦ meromorphicResidue_inverseMellin_of_cleared hg hne he ht⟩
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa [c] using mul_ne_zero hne
    (div_ne_zero (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)) hfac)

/-- An integrable power at each end controls a continuous vertical trace. -/
theorem integrable_of_power_tail {f : ℝ → ℂ} (hf : Continuous f)
    {β R C : ℝ} (hβ : 1 < β)
    (h : ∀ y : ℝ, R ≤ |y| → |y| ^ β * ‖f y‖ ≤ C) : Integrable f := by
  let B := max 1 R
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hpow : IntegrableOn (fun y : ℝ => C * y ^ (-β)) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) hB).const_mul C
  have hright : IntegrableOn f (Ioi B) := by
    apply hpow.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hB.trans hy
    have hd := h y (by rw [abs_of_pos hy0]; exact (le_max_right _ _).trans hy.le)
    rw [abs_of_pos hy0] at hd
    rw [Real.rpow_neg hy0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hy0 β), mul_comm]
    exact hd
  have hneg : IntegrableOn (fun y : ℝ => f (-y)) (Ioi B) := by
    apply hpow.mono' (hf.comp continuous_neg).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hB.trans hy
    have hd := h (-y) (by rw [abs_neg, abs_of_pos hy0]; exact (le_max_right _ _).trans hy.le)
    rw [abs_neg, abs_of_pos hy0] at hd
    rw [Real.rpow_neg hy0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hy0 β), mul_comm]
    exact hd
  have hneg' : IntegrableOn (fun y : ℝ => f (-y)) (Ioi (-(-B))) := by
    simpa only [neg_neg] using hneg
  have hleft : IntegrableOn f (Iio (-B)) := by
    simpa only [neg_neg] using hneg'.comp_neg_Iio
  have hmid : IntegrableOn f (Icc (-B) B) := hf.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Iio (-B) ∪ Icc (-B) B ∪ Ioi B = (univ : Set ℝ) := by
    ext y
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases hy : y < -B
    · exact Or.inl (Or.inl hy)
    · by_cases hy' : B < y
      · exact Or.inr hy'
      · exact Or.inl (Or.inr ⟨le_of_not_gt hy, le_of_not_gt hy'⟩)
  rw [← integrableOn_univ, ← hcover, integrableOn_union, integrableOn_union]
  exact ⟨⟨hleft, hmid⟩, hright⟩

private theorem mellinInv_eq_factor_integral {t : ℝ} (ht : 0 < t) (x : ℝ) (F : ℂ → ℂ) :
    mellinInv x F t =
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ,
        (inverseMellinFactor t * F) (verticalMellinPoint x y) := by
  unfold mellinInv
  simp only [Pi.mul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, inverseMellinFactor_eq ht,
    verticalMellinPoint]

/-- Sum the residues of the inverse Mellin integrand over distinct poles
of the continuation in the specified rectangle. -/
def mellinResidueWindow (F : ℂ → ℂ) (hF : Meromorphic F)
    (l r low high t : ℝ) : ℂ :=
  ∑ p ∈ rectanglePoles F l r low high hF.meromorphicOn,
    meromorphicResidue (inverseMellinFactor t * F) p

private theorem norm_interval_sub_integral_le_tail {f g : ℝ → ℂ} {a b M : ℝ}
    (hab : a ≤ b) (hf : Integrable f) (hg : Integrable g)
    (h : ∀ y, ‖g y‖ ≤ M * ‖f y‖) :
    ‖(∫ y in a..b, g y) - ∫ y, g y‖ ≤
      M * ((∫ y, ‖f y‖) - ∫ y in a..b, ‖f y‖) := by
  have h₁ := integral_add_compl measurableSet_Ioc hg (s := Ioc a b)
  have h₂ := integral_add_compl measurableSet_Ioc hf.norm (s := Ioc a b)
  rw [← h₁, ← h₂, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simp only [sub_add_cancel_left, norm_neg, add_sub_cancel_left]
  exact (norm_integral_le_integral_norm _).trans (by
    rw [← integral_const_mul]
    exact integral_mono (hg.norm.integrableOn) ((hf.norm.const_mul M).integrableOn) h)

private theorem inverseMellinFactor_uniform_norm_bound {J : Set ℝ} (hJ : IsCompact J)
    (hpos : J ⊆ Ioi 0) (l r : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ J, ∀ x ∈ Icc l r, ∀ y : ℝ,
      ‖inverseMellinFactor t (verticalMellinPoint x y)‖ ≤ B := by
  let w (t : ℝ) := max (t^(-l)) (t^(-r))
  have hw : ContinuousOn w J := by
    have H (q : ℝ) : ContinuousOn (fun t : ℝ ↦ t^q) J := fun t ht ↦
      (Real.continuousAt_rpow_const t q (.inl (hpos ht).ne')).continuousWithinAt
    exact continuous_max.comp_continuousOn ((H (-l)).prodMk (H (-r)))
  obtain ⟨M,hM⟩ := hJ.exists_bound_of_continuousOn hw
  refine ⟨max M 0, le_max_right _ _, fun t ht x hx y ↦ ?_⟩
  have ht' : 0 < t := hpos ht
  rw [inverseMellinFactor_eq ht', norm_cpow_eq_rpow_re_of_pos ht', neg_re, verticalMellinPoint_re]
  have hb : t ^ (-x) ≤ w t := by
    rcases le_total t 1 with h | h
    · exact (Real.rpow_le_rpow_of_exponent_ge ht' h (neg_le_neg hx.2)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le h (neg_le_neg hx.1)).trans (le_max_left _ _)
  exact hb.trans ((le_abs_self _).trans (((Real.norm_eq_abs _).symm ▸ hM t ht).trans (le_max_left _ _)))

/-- The recurrent distinct-pole Mellin sums converge uniformly on compact
subsets of the positive modulus axis. -/
theorem mellinInv_sub_tendstoUniformlyOn_residue_windows
    {F : ℂ → ℂ} {l r : ℝ} {low high : ℕ → ℝ}
    (hlr : l < r) (hF : MeromorphicNFOn F univ)
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hHorizontal : ∃ C : ℝ, ∀ᶠ j in atTop, ∀ x ∈ Icc l r,
      (AnalyticAt ℂ F (verticalMellinPoint x (low j)) ∧
        AnalyticAt ℂ F (verticalMellinPoint x (high j))) ∧
      (|low j| * ‖F (verticalMellinPoint x (low j))‖ ≤ C ∧
        |high j| * ‖F (verticalMellinPoint x (high j))‖ ≤ C))
    (hVertical : ∀ y : ℝ, AnalyticAt ℂ F (verticalMellinPoint l y) ∧
      AnalyticAt ℂ F (verticalMellinPoint r y))
    (hl : Complex.VerticalIntegrable F l) (hr : Complex.VerticalIntegrable F r)
    {J : Set ℝ} (hJ : IsCompact J) (hpos : J ⊆ Ioi 0) :
    TendstoUniformlyOn (fun j t ↦ mellinResidueWindow F
      (fun z ↦ (hF (mem_univ z)).meromorphicAt) l r (low j) (high j) t)
      (fun t ↦ mellinInv r F t - mellinInv l F t) atTop J := by
  obtain ⟨M,hM,hbound⟩ := inverseMellinFactor_uniform_norm_bound hJ hpos l r
  obtain ⟨C,hC⟩ := hHorizontal
  let tail (x : ℝ) (j : ℕ) :=
    (∫ y : ℝ, ‖F (verticalMellinPoint x y)‖) -
      ∫ y in low j..high j, ‖F (verticalMellinPoint x y)‖
  have htail (x : ℝ) (hf : Complex.VerticalIntegrable F x) : Tendsto (tail x) atTop (𝓝 0) := by
    have hn : Integrable (fun y : ℝ ↦ ‖F (verticalMellinPoint x y)‖) := hf.norm
    simpa only [tail, sub_self] using
      (intervalIntegral_tendsto_integral hn hlo hhi).const_sub
        (∫ y : ℝ, ‖F (verticalMellinPoint x y)‖)
  let H (y : ℝ) := (r-l) * (M * max C 0) * |y|⁻¹
  have hHlo : Tendsto (fun j ↦ H (low j)) atTop (𝓝 0) := by
    simpa only [H,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_abs_atBot_atTop.comp hlo)).const_mul ((r-l)*(M*max C 0))
  have hHhi : Tendsto (fun j ↦ H (high j)) atTop (𝓝 0) := by
    simpa only [H,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_abs_atTop_atTop.comp hhi)).const_mul ((r-l)*(M*max C 0))
  let err (j : ℕ) := (H (low j) + H (high j) + M * tail r j + M * tail l j) /
    ‖(2 * (Real.pi : ℂ) * I)‖
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, mul_zero, add_zero, zero_div] using
      (((hHlo.add hHhi).add ((htail r hr).const_mul M)).add
        ((htail l hl).const_mul M)).div_const ‖(2 * (Real.pi : ℂ) * I)‖
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [herr.eventually (eventually_lt_nhds hε), hC,
    hlo.eventually (eventually_lt_atBot 0), hhi.eventually (eventually_gt_atTop 0)]
    with j hjerr hjC hjlo hjhi t ht
  let u := low j
  let v := high j
  let G := inverseMellinFactor t * F
  have ht' : 0 < t := hpos ht
  have hG : MeromorphicNFOn G ([[l,r]] ×ℂ [[u,v]]) := fun {z} _ ↦
    (hF (mem_univ z)).smul_analytic (inverseMellinFactor_analytic t z) (exp_ne_zero _)
  have hGbound (x y : ℝ) (hx : x ∈ Icc l r) :
      ‖G (verticalMellinPoint x y)‖ ≤ M * ‖F (verticalMellinPoint x y)‖ := by
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hbound t ht x hx y) (norm_nonneg _))
  have hGa (x y : ℝ) (h : AnalyticAt ℂ F (verticalMellinPoint x y)) :
      AnalyticAt ℂ G (verticalMellinPoint x y) :=
    (inverseMellinFactor_analytic t _).mul h
  have hEdge : AnalyticOnNhd ℂ G (rectEdges l r u v) :=
    analyticOnNhd_rectEdges_of_lines hlr
      (fun x hx ↦ ⟨hGa _ _ (hjC x hx).1.1,hGa _ _ (hjC x hx).1.2⟩)
      (fun y ↦ ⟨hGa _ _ (hVertical y).1,hGa _ _ (hVertical y).2⟩)
  have ho (z : ℂ) : meromorphicOrderAt G z = meromorphicOrderAt F z :=
    meromorphicOrderAt_mul_of_ne_zero (inverseMellinFactor_analytic t z) (exp_ne_zero _)
  have hsum : (∑ p ∈ rectanglePoles G l r u v hG.meromorphicOn, meromorphicResidue G p) =
      mellinResidueWindow F (fun z ↦ (hF (mem_univ z)).meromorphicAt) l r u v t := by
    unfold mellinResidueWindow
    apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext p
    constructor
    · intro hp
      obtain ⟨hR,hP⟩ := (mem_rectanglePoles (f := G)).mp hp
      exact (mem_rectanglePoles (f := F)).mpr ⟨hR, (ho p) ▸ hP⟩
    · intro hp
      obtain ⟨hR,hP⟩ := (mem_rectanglePoles (f := F)).mp hp
      exact (mem_rectanglePoles (f := G)).mpr ⟨hR, (ho p).symm ▸ hP⟩
  have hrect := rectIntegral_meromorphic hlr (hjlo.trans hjhi) hG hEdge
  rw [rectIntegral_eq_edges,hsum] at hrect
  have hhorizontal (y : ℝ) (hy : 0 < |y|)
      (hyC : ∀ x ∈ Icc l r, |y| * ‖F (verticalMellinPoint x y)‖ ≤ C) :
      ‖∫ x in l..r, G (verticalMellinPoint x y)‖ ≤ H y := by
    have he : ∀ x ∈ Ι l r, ‖G (verticalMellinPoint x y)‖ ≤ M * max C 0 / |y| := by
      intro x hx
      rw [uIoc_of_le hlr.le] at hx
      have hx' : x ∈ Icc l r := Ioc_subset_Icc_self hx
      apply (le_div_iff₀ hy).mpr
      calc
        _ ≤ (M * ‖F (verticalMellinPoint x y)‖) * |y| :=
          mul_le_mul_of_nonneg_right (hGbound x y hx') hy.le
        _ = M * (|y| * ‖F (verticalMellinPoint x y)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ((hyC x hx').trans (le_max_left _ _)) hM
    refine (intervalIntegral.norm_integral_le_of_norm_le_const he).trans_eq ?_
    rw [abs_of_pos (sub_pos.mpr hlr)]
    dsimp [H]
    ring
  have htailG (x : ℝ) (hx : x ∈ Icc l r) (hf : Complex.VerticalIntegrable F x)
      (hreg : ∀ y, AnalyticAt ℂ F (verticalMellinPoint x y)) :
      ‖(∫ y in u..v, G (verticalMellinPoint x y)) - ∫ y, G (verticalMellinPoint x y)‖ ≤ M * tail x j := by
    have hcont : Continuous (fun y ↦ G (verticalMellinPoint x y)) := continuous_iff_continuousAt.mpr
      fun y ↦ (hGa _ _ (hreg y)).continuousAt.comp' (by unfold verticalMellinPoint; fun_prop)
    have hGint : Integrable (fun y ↦ G (verticalMellinPoint x y)) :=
      (hf.norm.const_mul M).mono' hcont.aestronglyMeasurable (.of_forall fun y ↦ hGbound x y hx)
    exact norm_interval_sub_integral_le_tail (hjlo.trans hjhi).le hf hGint (hGbound x · hx)
  let L := (∫ y in u..v, G (verticalMellinPoint l y)) - ∫ y, G (verticalMellinPoint l y)
  let R := (∫ y in u..v, G (verticalMellinPoint r y)) - ∫ y, G (verticalMellinPoint r y)
  have hdiff :
      mellinResidueWindow F (fun z ↦ (hF (mem_univ z)).meromorphicAt) l r u v t -
        (mellinInv r F t - mellinInv l F t) =
      ((∫ x in l..r, G (verticalMellinPoint x u)) - (∫ x in l..r, G (verticalMellinPoint x v)) +
        I * R - I * L) / (2 * (Real.pi : ℂ) * I) := by
    have hScale (x : ℝ) : mellinInv x F t * (2 * (Real.pi : ℂ) * I) =
        I * ∫ y : ℝ, G (verticalMellinPoint x y) := by
      rw [mellinInv_eq_factor_integral ht' x F]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
      <;> ring
    apply (eq_div_iff Complex.two_pi_I_ne_zero).mpr
    rw [sub_mul, sub_mul, hScale, hScale, mul_comm _ (2 * (Real.pi : ℂ) * I)]
    change (∫ x in l..r, G (verticalMellinPoint x u)) -
      (∫ x in l..r, G (verticalMellinPoint x v)) +
      I * (∫ y in u..v, G (verticalMellinPoint r y)) -
      I * (∫ y in u..v, G (verticalMellinPoint l y)) = _ at hrect
    rw [← hrect]
    dsimp [L,R]
    ring
  have hest : ‖mellinResidueWindow F (fun z ↦ (hF (mem_univ z)).meromorphicAt) l r u v t -
      (mellinInv r F t - mellinInv l F t)‖ ≤ err j := by
    rw [hdiff,norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) (le_refl _)).trans ?_
    refine (add_le_add (add_le_add (norm_sub_le _ _) (le_refl _)) (le_refl _)).trans ?_
    simp only [norm_mul,Complex.norm_I,one_mul]
    exact add_le_add (add_le_add (add_le_add
      (hhorizontal u (abs_pos.mpr hjlo.ne) fun x hx ↦ (hjC x hx).2.1)
      (hhorizontal v (abs_pos.mpr hjhi.ne') fun x hx ↦ (hjC x hx).2.2))
      (htailG r ⟨hlr.le,le_rfl⟩ hr fun y ↦ (hVertical y).2))
      (htailG l ⟨le_rfl,hlr.le⟩ hl fun y ↦ (hVertical y).1)
  rw [dist_eq_norm]
  exact (by simpa [norm_sub_rev] using hest : _ ≤ err j).trans_lt hjerr

/-- The finite-pole Mellin contour shift with the full integrable range
`β > 1` and the decay bound imposed only at large imaginary heights. -/
theorem mellinInv_sub_eq_residue_sum_of_power_decay
    {F : ℂ → ℂ} {l r : ℝ} (hlr : l < r)
    (hF : MeromorphicNFOn F (Complex.re ⁻¹' Icc l r))
    (S : Finset ℂ) (hS : ∀ p ∈ S, p.re ∈ Ioo l r)
    (hpoles : ∀ p : ℂ, p.re ∈ Icc l r → (meromorphicOrderAt F p < 0 ↔ p ∈ S))
    {β R C : ℝ} (hβ : 1 < β)
    (hdecay : ∀ z : ℂ, z.re ∈ Icc l r → R ≤ |z.im| → |z.im| ^ β * ‖F z‖ ≤ C)
    {t : ℝ} (ht : 0 < t) :
    mellinInv r F t - mellinInv l F t =
      ∑ p ∈ S, meromorphicResidue (inverseMellinFactor t * F) p := by
  let Φ := inverseMellinFactor t
  let G := Φ * F
  have hG : MeromorphicNFOn G (Complex.re ⁻¹' Icc l r) := fun {z} hz =>
    (hF hz).smul_analytic (inverseMellinFactor_analytic t z) (Complex.exp_ne_zero _)
  have ho (z : ℂ) : meromorphicOrderAt G z = meromorphicOrderAt F z :=
    meromorphicOrderAt_mul_of_ne_zero (inverseMellinFactor_analytic t z) (Complex.exp_ne_zero _)
  have horder (x y : ℝ) (hx : x ∈ Icc l r) : AnalyticAt ℂ G (verticalMellinPoint x y) ↔
      verticalMellinPoint x y ∉ S := by
    have hx' : verticalMellinPoint x y ∈ Complex.re ⁻¹' Icc l r := by simpa
    rw [← (hG hx').meromorphicOrderAt_nonneg_iff_analyticAt, ho, ← not_lt, hpoles _ hx']
  have hleft (y : ℝ) : AnalyticAt ℂ G (verticalMellinPoint l y) :=
    (horder l y ⟨le_rfl, hlr.le⟩).mpr fun h =>
      (lt_irrefl l) (by simpa using (hS _ h).1)
  have hright (y : ℝ) : AnalyticAt ℂ G (verticalMellinPoint r y) :=
    (horder r y ⟨hlr.le, le_rfl⟩).mpr fun h =>
      (lt_irrefl r) (by simpa using (hS _ h).2)
  let D : ℝ := max (t ^ (-l)) (t ^ (-r))
  have hD (x y : ℝ) (hx : x ∈ Icc l r) : ‖Φ (verticalMellinPoint x y)‖ ≤ D := by
    rw [show Φ (verticalMellinPoint x y) = (t : ℂ) ^ (-verticalMellinPoint x y) from
      inverseMellinFactor_eq ht _, norm_cpow_eq_rpow_re_of_pos ht, neg_re, verticalMellinPoint_re]
    rcases le_total t 1 with h | h
    · exact (Real.rpow_le_rpow_of_exponent_ge ht h (neg_le_neg hx.2)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le h (neg_le_neg hx.1)).trans (le_max_left _ _)
  have hGdec (x y : ℝ) (hx : x ∈ Icc l r) (hy : R ≤ |y|) :
      |y| ^ β * ‖G (verticalMellinPoint x y)‖ ≤ D * C := by
    calc
      _ = ‖Φ (verticalMellinPoint x y)‖ * (|y| ^ β * ‖F (verticalMellinPoint x y)‖) := by
        simp [G]
        ring
      _ ≤ D * C := mul_le_mul (hD x y hx)
        (by simpa using hdecay (verticalMellinPoint x y) (by simpa using hx) (by simpa using hy))
        (by positivity) ((norm_nonneg _).trans (hD x y hx))
  have hInt (x : ℝ) (hx : x ∈ Icc l r) (ha : ∀ y, AnalyticAt ℂ G (verticalMellinPoint x y)) :
      Integrable (fun y : ℝ => G (verticalMellinPoint x y)) := by
    refine integrable_of_power_tail ?_ hβ (fun y hy => hGdec x y hx hy)
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact (ha y).continuousAt.comp (f := fun y => verticalMellinPoint x y)
      (by unfold verticalMellinPoint; fun_prop)
  let low : ℕ → ℝ := fun j => -(j : ℝ)
  let high : ℕ → ℝ := fun j => j
  have hLow : Tendsto low atTop atBot := tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hHigh : Tendsto high atTop atTop := tendsto_natCast_atTop_atTop
  have hcontains : ∀ᶠ j in atTop, ∀ p ∈ S, p.im ∈ Ioo (low j) (high j) := by
    apply S.eventually_all.mpr
    intro p _
    exact (hLow.eventually (eventually_lt_atBot p.im)).and (hHigh.eventually (eventually_gt_atTop p.im))
  have hH : ∃ K : ℝ, ∀ᶠ j in atTop, ∀ x ∈ Icc l r,
      (AnalyticAt ℂ G (verticalMellinPoint x (low j)) ∧
        AnalyticAt ℂ G (verticalMellinPoint x (high j))) ∧
      (|low j| * ‖G (verticalMellinPoint x (low j))‖ ≤ K ∧
        |high j| * ‖G (verticalMellinPoint x (high j))‖ ≤ K) := by
    refine ⟨D * C, ?_⟩
    filter_upwards [hcontains, hHigh.eventually (eventually_ge_atTop (max 1 R))] with j hj hlarge x hx
    have hbound (y : ℝ) (hy : max 1 R ≤ |y|) :
        |y| * ‖G (verticalMellinPoint x y)‖ ≤ D * C := by
      have hpow : |y| ≤ |y| ^ β := by
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le ((le_max_left _ _).trans hy) hβ.le)
      exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
        (hGdec x y hx ((le_max_right _ _).trans hy))
    refine ⟨⟨(horder x _ hx).mpr ?_, (horder x _ hx).mpr ?_⟩, hbound _ ?_, hbound _ ?_⟩
    · intro hp
      exact (lt_irrefl (low j)) (by simpa using (hj _ hp).1)
    · intro hp
      exact (lt_irrefl (high j)) (by simpa using (hj _ hp).2)
    · change max 1 R ≤ |-(j : ℝ)|
      simpa only [abs_neg, abs_of_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ)), high] using hlarge
    · simpa [abs_of_nonneg (show 0 ≤ high j from Nat.cast_nonneg j)] using hlarge
  have hlim := asymptotic_residue_of_integrable hlr hG hLow hHigh hH (fun y => ⟨hleft y, hright y⟩)
    (hInt l ⟨le_rfl, hlr.le⟩ hleft) (hInt r ⟨hlr.le, le_rfl⟩ hright)
  have hRect (j : ℕ) : MeromorphicOn G ([[l, r]] ×ℂ [[low j, high j]]) := by
    intro z hz
    exact (hG (show z ∈ Complex.re ⁻¹' Icc l r from by
      have h := (Complex.mem_reProdIm.mp hz).1
      simpa [uIcc_of_le hlr.le] using h)).meromorphicAt
  have hs : (fun j => ∑ p ∈ rectanglePoles G l r (low j) (high j) (hRect j),
      meromorphicResidue G p) =ᶠ[atTop] fun _ : ℕ => ∑ p ∈ S, meromorphicResidue G p := by
    filter_upwards [hcontains, hLow.eventually (eventually_lt_atBot 0),
      hHigh.eventually (eventually_gt_atTop 0)] with j hj hlj hhj
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    refine (mem_rectanglePoles (hf := hRect j) (z := p)).trans ?_
    rw [Complex.mem_reProdIm, uIcc_of_le hlr.le, uIcc_of_le (hlj.trans hhj).le, ho]
    constructor
    · rintro ⟨⟨hp, _⟩, hpol⟩
      exact (hpoles p hp).mp hpol
    · intro hp
      have hx := Ioo_subset_Icc_self (hS p hp)
      exact ⟨⟨hx, Ioo_subset_Icc_self (hj p hp)⟩, (hpoles p hx).mpr hp⟩
  have heq := tendsto_nhds_unique (hlim.congr' hs) tendsto_const_nhds
  rw [mellinInv_eq_factor_integral ht r F, mellinInv_eq_factor_integral ht l F]
  rw [← heq]
  change _ = (I * (∫ y : ℝ, G (verticalMellinPoint r y)) -
    I * (∫ y : ℝ, G (verticalMellinPoint l y))) / (2 * (Real.pi : ℂ) * I)
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Complex.I_ne_zero, hp]
  rfl

private theorem mellinSchwartzAt_verticalIntegrable {φ : ℝ → ℂ} {a B : ℝ}
    (haB : a < B) (hw : ∀ σ ∈ Icc a B, MellinSchwartzAt φ σ) :
    Complex.VerticalIntegrable (mellin φ) B := by
  obtain ⟨g, hg⟩ := (mellin_uniform_riemann_lebesgue haB hw).2.2.1 B ⟨haB.le, le_rfl⟩
  change Integrable (fun y : ℝ => mellin φ (verticalMellinPoint B y))
  have he : (⇑g : ℝ → ℂ) = fun y => mellin φ (verticalMellinPoint B y) := by
    funext y
    rw [congrFun hg y]
    exact congrArg (mellin φ) (Complex.ext (by simp) (by simp))
  rw [← he]
  exact g.integrable

set_option quotPrecheck false in
local notation "mellinOpenStrip" =>
  (fun (a : ℝ) (b : WithTop ℝ) => {z : ℂ | a < z.re ∧ (z.re : WithTop ℝ) < b})

/-- Corrected Theorem B.2.1.7(1). The growth bound is required only above
a finite height. The continuation uses its meromorphic normal representative
so it is analytic at every point of nonnegative order. -/
theorem mellin_asymptoticExpansion_of_meromorphic
    (a A ε B : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hAε : A + ε < 0) (haB : a < B) (hB : (B : WithTop ℝ) < b)
    (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (hw : ∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b → MellinSchwartzAt φ σ)
    (poles : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ α ∈ poles, 1 ≤ m α)
    (hpoles : ∀ α ∈ poles, (-α).re ∈ Ioc (A + ε) a)
    (F : ℂ → ℂ) (hF : MeromorphicNFOn F (mellinOpenStrip A b))
    (hAgree : EqOn F (mellin φ) (mellinOpenStrip a b))
    (hOrders : ∀ α ∈ poles, meromorphicOrderAt F (-α) = -((m α : ℕ) : ℤ))
    (hNoOther : ∀ z ∈ mellinOpenStrip A b, -z ∉ poles → 0 ≤ meromorphicOrderAt F z)
    (hDec : ∃ β > (1 : ℝ), ∃ C R : ℝ, ∀ z : ℂ,
      z.re ∈ Icc (A + ε / 2) B → R ≤ |z.im| → ‖z‖ ^ β * ‖F z‖ ≤ C) :
    ∃ c : ℂ → ℕ → ℂ, (∀ α ∈ poles, c α (m α - 1) ≠ 0) ∧
      (fun t : ℝ => φ t - ∑ α ∈ poles, ∑ k ∈ Finset.range (m α),
        c α k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k)
        =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(A + ε)) := by
  classical
  let l := A + ε
  have hlB : l < B := hAε.trans (ha.trans haB)
  have hsub : Complex.re ⁻¹' Icc l B ⊆ mellinOpenStrip A b := by
    intro z hz
    change z.re ∈ Icc l B at hz
    exact ⟨(lt_add_of_pos_right A hε).trans_le hz.1, (WithTop.coe_le_coe.mpr hz.2).trans_lt hB⟩
  have hFs : MeromorphicNFOn F (Complex.re ⁻¹' Icc l B) := fun _ hz => hF (hsub hz)
  let S := poles.image Neg.neg
  have hS (p : ℂ) : p ∈ S ↔ -p ∈ poles := by
    simp only [S, Finset.mem_image]
    constructor
    · rintro ⟨α, hα, rfl⟩
      simpa using hα
    · intro hp
      exact ⟨-p, hp, neg_neg p⟩
  have hwhere (p : ℂ) (hp : p ∈ S) : p.re ∈ Ioo l B := by
    have h := hpoles (-p) ((hS p).mp hp)
    rw [neg_neg] at h
    exact ⟨h.1, h.2.trans_lt haB⟩
  have hExact (p : ℂ) (hp : p.re ∈ Icc l B) :
      meromorphicOrderAt F p < 0 ↔ p ∈ S := by
    rw [hS]
    constructor
    · intro ho
      by_contra hn
      exact (not_lt_of_ge (hNoOther p (hsub hp) hn)) ho
    · intro h
      have hh := hOrders (-p) h
      rw [neg_neg] at hh
      rw [hh]
      exact_mod_cast (show -(m (-p) : ℤ) < 0 by exact neg_neg_of_pos (by exact_mod_cast hm (-p) h))
  obtain ⟨β, hβ, C, R, hd⟩ := hDec
  have hbound (z : ℂ) (hz : z.re ∈ Icc l B) (hy : R ≤ |z.im|) :
      |z.im| ^ β * ‖F z‖ ≤ C := by
    refine (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_im_le_norm z) (by linarith : 0 ≤ β))
      (norm_nonneg _)).trans (hd z ⟨?_, hz.2⟩ hy)
    dsimp [l] at hz
    linarith [hz.1]
  have hres (α : ℂ) (hα : α ∈ poles) :
      ∃ c : ℕ → ℂ, c (m α - 1) ≠ 0 ∧ ∀ t : ℝ, 0 < t →
        meromorphicResidue (inverseMellinFactor t * F) (-α) =
          ∑ k ∈ Finset.range (m α), c k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k := by
    have hp := hpoles α hα
    have hmα := hm α hα
    have hmem : -α ∈ mellinOpenStrip A b := hsub ⟨hp.1.le, hp.2.trans haB.le⟩
    have hf := (hF hmem).meromorphicAt
    have hn : m α - 1 + 1 = m α := by omega
    have horder : meromorphicOrderAt F (-α) = (-(((m α - 1 : ℕ) : ℤ) + 1) : ℤ) := by
      rw [hOrders α hα]
      have hcast : ((m α - 1 + 1 : ℕ) : ℤ) = (m α : ℤ) := by rw [hn]
      push_cast at hcast
      rw [hcast, WithTop.LinearOrderedAddCommGroup.coe_neg]
    obtain ⟨c, hc, hres⟩ := meromorphicResidue_inverseMellin_powerLog hf horder
    exact ⟨c, hc, fun t ht => by simpa only [hn, neg_neg] using hres t ht⟩
  let c (α : ℂ) : ℕ → ℂ := if h : α ∈ poles then (hres α h).choose else 0
  have hcoeff (α : ℂ) (hα : α ∈ poles) := (hres α hα).choose_spec
  refine ⟨c, fun α hα => ?_, ?_⟩
  · dsimp only [c]
    rw [dite_eq_left hα]
    exact (hcoeff α hα).1
  · apply (mellinInv_isBigO_nhdsGT_zero l F).congr' _ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hAgreeLine (y : ℝ) : F (verticalMellinPoint B y) = mellin φ (verticalMellinPoint B y) := by
      apply hAgree
      simpa using And.intro haB hB
    have hInversion : mellinInv B F t = φ t := by
      have hInt : Complex.VerticalIntegrable (mellin φ) B := by
        let d := (a + B) / 2
        have had : a < d := by dsimp [d]; linarith
        have hdB : d < B := by dsimp [d]; linarith
        exact mellinSchwartzAt_verticalIntegrable hdB fun σ hσ =>
          hw σ (had.trans_le hσ.1) ((WithTop.coe_le_coe.mpr hσ.2).trans_lt hB)
      have hfun : mellinInv B F t = mellinInv B (mellin φ) t := by
        rw [mellinInv_eq_factor_integral ht, mellinInv_eq_factor_integral ht]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun y => by
          dsimp only [Pi.mul_apply]
          rw [hAgreeLine])
      rw [hfun]
      exact mellinInv_mellin_eq B φ ht
        (mellinConvergent_of_schwartzAt (s := (B : ℂ)) (by simpa using hw B haB hB))
        hInt (hφ.continuousOn.continuousAt (isOpen_Ioi.mem_nhds ht))
    have hshift := mellinInv_sub_eq_residue_sum_of_power_decay hlB hFs S hwhere hExact hβ hbound ht
    have hsum :
        (∑ p ∈ S, meromorphicResidue (inverseMellinFactor t * F) p) =
          ∑ α ∈ poles, ∑ k ∈ Finset.range (m α),
            c α k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k := by
      rw [show S = poles.image Neg.neg from rfl, Finset.sum_image (fun x _ y _ h => neg_injective h)]
      apply Finset.sum_congr rfl
      intro α hα
      dsimp only [c]
      rw [dite_eq_left hα]
      exact (hcoeff α hα).2 t ht
    rw [hInversion, hsum] at hshift
    linear_combination -hshift

/-- The converse, B.2.1.7(2), on the same logarithmic Schwartz model
as the forward asymptotic theorem. -/
theorem mellin_meromorphic_of_asymptoticExpansion
    (a A : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hA : A < 0) (hab : (a : WithTop ℝ) < b)
    (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (hw : ∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b → MellinSchwartzAt φ σ)
    (poles : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ α ∈ poles, 1 ≤ m α)
    (hpoles : ∀ α ∈ poles, (-α).re ∈ Ioc A a) (c : ℂ → ℕ → ℂ)
    (hc : ∀ α ∈ poles, c α (m α - 1) ≠ 0)
    (hAsymptotic : (fun t : ℝ => φ t - ∑ α ∈ poles, ∑ k ∈ Finset.range (m α),
      c α k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k)
        =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-A)) :
    ∃ F : ℂ → ℂ, MeromorphicNFOn F (mellinOpenStrip A b) ∧
      (∀ z ∈ mellinOpenStrip a b, HasMellin φ z (F z)) ∧
      (∀ α ∈ poles, meromorphicOrderAt F (-α) = -((m α : ℕ) : ℤ)) ∧
      ∀ z ∈ mellinOpenStrip A b, -z ∉ poles → 0 ≤ meromorphicOrderAt F z := by
  refine exists_meromorphic_mellin_of_asymptoticExpansion a A b ha hA hab φ hφ ?_
    poles m hm hpoles c hc hAsymptotic
  intro σ hσ hσb
  obtain ⟨g, hg⟩ := mellinSchwartzAt_iff_positive_log.mp (hw σ hσ hσb)
  exact ⟨g, fun x => by rw [congrFun hg x, Complex.real_smul]⟩

end
end Masullo
