import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex Filter MeasureTheory Set
open scoped Interval

namespace Masullo

private noncomputable def affineIntegral (f : ℂ → ℂ) (d e : ℂ) (u v : ℝ) : ℂ :=
  ∫ x in u..v, d * f (d * (x : ℂ) + e)

private theorem affineIntegral_eq_sub {f P : ℂ → ℂ} {d e : ℂ} {u v : ℝ}
    (hf : ContinuousOn (fun x : ℝ => f (d * (x : ℂ) + e)) [[u, v]])
    (hP : ∀ x ∈ [[u, v]], HasDerivAt P (f (d * (x : ℂ) + e)) (d * (x : ℂ) + e)) :
    affineIntegral f d e u v = P (d * (v : ℂ) + e) - P (d * (u : ℂ) + e) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hd := (((hasDerivAt_id' (x : ℂ)).const_mul d).add_const e)
    simpa [mul_comm] using ((hP x hx).comp (x : ℂ) hd).comp_ofReal
  · exact (continuousOn_const.mul hf).intervalIntegrable

/-- The counterclockwise integral around the rectangle with opposite corners
`(a,c)` and `(b,d)`. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  affineIntegral f 1 ((c : ℂ) * I) a b - affineIntegral f 1 ((d : ℂ) * I) a b +
  affineIntegral f I b c d - affineIntegral f I a c d

-- This form is convenient when applying Cauchy–Goursat and when passing to the infinite contour.
theorem rectIntegral_eq_edges (f : ℂ → ℂ) (a b c d : ℝ) :
    rectIntegral f a b c d =
      (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
      I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I)) := by
  simp only [rectIntegral, affineIntegral, one_mul, intervalIntegral.integral_const_mul]
  simp only [mul_comm I, add_comm (_ * I)]

theorem rectIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f ([[a, b]] ×ℂ [[c, d]])) :
    rectIntegral f a b c d = 0 := by
  rw [rectIntegral_eq_edges]
  simpa [smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, c⟩ ⟨b, d⟩ hf

private theorem inv_affineIntegral_eq_log_sub {p d e : ℂ} {u v : ℝ}
    (h : ∀ x ∈ [[u, v]], d * (x : ℂ) + e - p ∈ slitPlane) :
    affineIntegral (fun z => (z - p)⁻¹) d e u v =
      log (d * (v : ℂ) + e - p) - log (d * (u : ℂ) + e - p) := by
  apply affineIntegral_eq_sub (P := fun z => log (z - p))
  · exact (show Continuous (fun x : ℝ => d * (x : ℂ) + e - p) by fun_prop).continuousOn.inv₀
      (fun x hx => slitPlane_ne_zero (h x hx))
  · intro x hx
    have hd := (hasDerivAt_log (h x hx)).comp (d * (x : ℂ) + e)
      ((hasDerivAt_id' (d * (x : ℂ) + e)).sub_const p)
    rw [mul_one] at hd
    exact hd

private theorem inv_affineIntegral_eq_log_neg_sub {p d e : ℂ} {u v : ℝ}
    (h : ∀ x ∈ [[u, v]], p - (d * (x : ℂ) + e) ∈ slitPlane) :
    affineIntegral (fun z => (z - p)⁻¹) d e u v =
      log (p - (d * (v : ℂ) + e)) - log (p - (d * (u : ℂ) + e)) := by
  apply affineIntegral_eq_sub (P := fun z => log (p - z))
  · exact (show Continuous (fun x : ℝ => d * (x : ℂ) + e - p) by fun_prop).continuousOn.inv₀
      (fun x hx => sub_ne_zero.mpr (sub_ne_zero.mp (slitPlane_ne_zero (h x hx))).symm)
  · intro x hx
    have hd := (hasDerivAt_log (h x hx)).comp _
      ((hasDerivAt_id' (d * (x : ℂ) + e)).const_sub p)
    have he : p - (d * (x : ℂ) + e) = -(d * (x : ℂ) + e - p) := by ring
    change HasDerivAt (fun z => log (p - z)) ((p - (d * (x : ℂ) + e))⁻¹ * -1) _ at hd
    rw [he, inv_neg, mul_neg, mul_one, neg_neg] at hd
    exact hd

private theorem log_sub_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  simp [Complex.log, arg_neg_eq_arg_sub_pi_of_im_pos hz, sub_mul]

private theorem log_sub_log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  simp [Complex.log, arg_neg_eq_arg_add_pi_of_im_neg hz, add_mul]

/-- The residue contributed by the reciprocal kernel at an interior point. -/
theorem rectIntegral_sub_inv {p : ℂ} {a b c d : ℝ}
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d) :
    rectIntegral (fun z => (z - p)⁻¹) a b c d = 2 * Real.pi * I := by
  have hbottom (x : ℝ) (_ : x ∈ [[a, b]]) :
      1 * (x : ℂ) + (c : ℂ) * I - p ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inr ?_)
    simpa [Complex.mul_im] using (sub_neg.mpr hc).ne
  have htop (x : ℝ) (_ : x ∈ [[a, b]]) :
      1 * (x : ℂ) + (d : ℂ) * I - p ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inr ?_)
    simpa [Complex.mul_im] using (sub_pos.mpr hd).ne'
  have hright (y : ℝ) (_ : y ∈ [[c, d]]) :
      I * (y : ℂ) + (b : ℂ) - p ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simpa [Complex.mul_re] using sub_pos.mpr hb
  have hleft (y : ℝ) (_ : y ∈ [[c, d]]) :
      p - (I * (y : ℂ) + (a : ℂ)) ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simpa [Complex.mul_re] using sub_pos.mpr ha
  unfold rectIntegral
  rw [inv_affineIntegral_eq_log_sub hbottom, inv_affineIntegral_eq_log_sub htop,
    inv_affineIntegral_eq_log_sub hright, inv_affineIntegral_eq_log_neg_sub hleft]
  simp only [one_mul]
  have hlo := log_sub_log_neg_of_im_neg (z := (a : ℂ) + (c : ℂ) * I - p)
    (by simpa [Complex.mul_im] using sub_neg.mpr hc)
  have hhi := log_sub_log_neg_of_im_pos (z := (a : ℂ) + (d : ℂ) * I - p)
    (by simpa [Complex.mul_im] using sub_pos.mpr hd)
  rw [show -(↑a + (c : ℂ) * I - p) = p - (I * (c : ℂ) + ↑a) by ring] at hlo
  rw [show -(↑a + (d : ℂ) * I - p) = p - (I * (d : ℂ) + ↑a) by ring] at hhi
  rw [mul_comm I (d : ℂ), add_comm _ (b : ℂ), mul_comm I (c : ℂ), add_comm _ (b : ℂ)]
  rw [mul_comm I (d : ℂ), add_comm _ (a : ℂ)] at hhi
  rw [mul_comm I (c : ℂ), add_comm _ (a : ℂ)] at hlo
  simp only [add_comm ((d : ℂ) * I) (a : ℂ),
    add_comm ((c : ℂ) * I) (a : ℂ)]
  linear_combination hhi - hlo


private theorem zpow_affineIntegral_eq_sub {p d e : ℂ} {u v : ℝ} {m : ℤ}
    (hm : m ≠ -1) (h : ∀ x ∈ [[u, v]], d * (x : ℂ) + e ≠ p) :
    affineIntegral (fun z => (z - p) ^ m) d e u v =
      (d * (v : ℂ) + e - p) ^ (m + 1) / ((m + 1 : ℤ) : ℂ) -
      (d * (u : ℂ) + e - p) ^ (m + 1) / ((m + 1 : ℤ) : ℂ) := by
  apply affineIntegral_eq_sub (P := fun z => (z - p) ^ (m + 1) / ((m + 1 : ℤ) : ℂ))
  · exact (show Continuous (fun x : ℝ => d * (x : ℂ) + e - p) by fun_prop).continuousOn.zpow₀ m
      (fun x hx => Or.inl (sub_ne_zero.mpr (h x hx)))
  · intro x hx
    let q := d * (x : ℂ) + e
    have hd := (hasDerivAt_zpow (m + 1) (q - p) (Or.inl (sub_ne_zero.mpr (h x hx)))).comp
      q ((hasDerivAt_id' q).sub_const p)
    have h0 : ((m + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
    have hder := hd.div_const ((m + 1 : ℤ) : ℂ)
    rw [mul_one, add_sub_cancel_right, mul_comm, mul_div_cancel_right₀ _ h0] at hder
    exact hder

/-- All Laurent powers other than the residue term integrate to zero. -/
theorem rectIntegral_sub_zpow_of_ne_neg_one {p : ℂ} {a b c d : ℝ} {m : ℤ}
    (hm : m ≠ -1) (ha : a ≠ p.re) (hb : b ≠ p.re) (hc : c ≠ p.im) (hd : d ≠ p.im) :
    rectIntegral (fun z => (z - p) ^ m) a b c d = 0 := by
  have hh (t : ℝ) (ht : t ≠ p.im) (x : ℝ) (_ : x ∈ [[a, b]]) :
      1 * (x : ℂ) + (t : ℂ) * I ≠ p := fun h => ht (by simpa [Complex.mul_im] using congrArg im h)
  have hv (t : ℝ) (ht : t ≠ p.re) (y : ℝ) (_ : y ∈ [[c, d]]) :
      I * (y : ℂ) + (t : ℂ) ≠ p := fun h => ht (by simpa [Complex.mul_re] using congrArg re h)
  unfold rectIntegral
  rw [zpow_affineIntegral_eq_sub hm (hh c hc), zpow_affineIntegral_eq_sub hm (hh d hd),
    zpow_affineIntegral_eq_sub hm (hv b hb), zpow_affineIntegral_eq_sub hm (hv a ha)]
  simp only [one_mul, mul_comm I, add_comm (_ * I)]
  ring

/-- The four edges of the closed rectangle, including its corners. -/
def rectEdges (a b c d : ℝ) : Set ℂ :=
  ([[a, b]] ×ℂ ({c, d} : Set ℝ)) ∪ (({a, b} : Set ℝ) ×ℂ [[c, d]])

private theorem mem_rectEdges_horizontal {a b c d x t : ℝ} (hx : x ∈ [[a, b]])
    (ht : t ∈ ({c, d} : Set ℝ)) : (x : ℂ) + (t : ℂ) * I ∈ rectEdges a b c d := by
  exact Or.inl (by simpa [Complex.mem_reProdIm, Complex.mul_re, Complex.mul_im] using And.intro hx ht)

private theorem mem_rectEdges_vertical {a b c d y t : ℝ} (hy : y ∈ [[c, d]])
    (ht : t ∈ ({a, b} : Set ℝ)) : I * (y : ℂ) + (t : ℂ) ∈ rectEdges a b c d := by
  exact Or.inr (by simpa [Complex.mem_reProdIm, Complex.mul_re, Complex.mul_im] using And.intro ht hy)

theorem rectIntegral_congr_edges {f g : ℂ → ℂ} {a b c d : ℝ}
    (h : EqOn f g (rectEdges a b c d)) : rectIntegral f a b c d = rectIntegral g a b c d := by
  unfold rectIntegral affineIntegral
  congr 1 <;> first
    | exact intervalIntegral.integral_congr (fun x hx => by rw [h (mem_rectEdges_vertical hx (by simp))])
    | congr 1
      · congr 1 <;> apply intervalIntegral.integral_congr <;> intro x hx
        · simpa only [one_mul] using h (mem_rectEdges_horizontal (t := c) hx (by simp))
        · simpa only [one_mul] using h (mem_rectEdges_horizontal (t := d) hx (by simp))
      · exact intervalIntegral.integral_congr (fun x hx => by rw [h (mem_rectEdges_vertical hx (by simp))])

private theorem affineIntegrable_of_continuousOn_edges {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (rectEdges a b c d)) :
    (∀ t ∈ ({c, d} : Set ℝ),
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I)) volume a b) ∧
    (∀ t ∈ ({a, b} : Set ℝ),
      IntervalIntegrable (fun y : ℝ => I * f (I * (y : ℂ) + (t : ℂ))) volume c d) := by
  constructor
  · intro t ht
    exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (t : ℂ) * I).continuousOn
      (fun _ hx => mem_rectEdges_horizontal hx ht)).intervalIntegrable
  · intro t ht
    exact (continuousOn_const.mul (hf.comp
      (by fun_prop : Continuous fun y : ℝ => I * (y : ℂ) + (t : ℂ)).continuousOn
      (fun _ hy => mem_rectEdges_vertical hy ht))).intervalIntegrable

theorem rectIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (rectEdges a b c d)) (hg : ContinuousOn g (rectEdges a b c d)) :
    rectIntegral (fun z => f z + g z) a b c d = rectIntegral f a b c d + rectIntegral g a b c d := by
  obtain ⟨hfh, hfv⟩ := affineIntegrable_of_continuousOn_edges hf
  obtain ⟨hgh, hgv⟩ := affineIntegrable_of_continuousOn_edges hg
  simp only [rectIntegral, affineIntegral, one_mul, mul_add]
  rw [intervalIntegral.integral_add (hfh c (by simp)) (hgh c (by simp)),
    intervalIntegral.integral_add (hfh d (by simp)) (hgh d (by simp)),
    intervalIntegral.integral_add (hfv b (by simp)) (hgv b (by simp)),
    intervalIntegral.integral_add (hfv a (by simp)) (hgv a (by simp))]
  ring

theorem rectIntegral_const_mul (f : ℂ → ℂ) (k : ℂ) (a b c d : ℝ) :
    rectIntegral (fun z => k * f z) a b c d = k * rectIntegral f a b c d := by
  simp only [rectIntegral, affineIntegral, mul_left_comm _ k, intervalIntegral.integral_const_mul]
  ring

theorem rectIntegral_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℂ} {a b c d : ℝ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectEdges a b c d)) :
    rectIntegral (fun z => ∑ i ∈ s, f i z) a b c d = ∑ i ∈ s, rectIntegral (f i) a b c d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectIntegral, affineIntegral]
  | insert i t hit ih =>
    have ht : ∀ j ∈ t, ContinuousOn (f j) (rectEdges a b c d) :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hit]
    rw [rectIntegral_add (hf i (Finset.mem_insert_self i t)) (continuousOn_finsetSum _ ht), ih ht]


theorem point_notMem_rectEdges {p : ℂ} {a b c d : ℝ}
    (ha : a ≠ p.re) (hb : b ≠ p.re) (hc : c ≠ p.im) (hd : d ≠ p.im) :
    p ∉ rectEdges a b c d := by
  simp [rectEdges, Complex.mem_reProdIm, Ne.symm ha, Ne.symm hb, Ne.symm hc, Ne.symm hd]

theorem rectEdges_subset {a b c d : ℝ} :
    rectEdges a b c d ⊆ ([[a, b]] ×ℂ [[c, d]]) := by
  rintro z (hz | hz)
  · obtain ⟨hx, hy⟩ := Complex.mem_reProdIm.mp hz
    rcases (mem_insert_iff.mp hy) with rfl | hy
    · exact Complex.mem_reProdIm.mpr ⟨hx, left_mem_uIcc⟩
    · exact Complex.mem_reProdIm.mpr ⟨hx, (mem_singleton_iff.mp hy).symm ▸ right_mem_uIcc⟩
  · obtain ⟨hx, hy⟩ := Complex.mem_reProdIm.mp hz
    rcases (mem_insert_iff.mp hx) with rfl | hx
    · exact Complex.mem_reProdIm.mpr ⟨left_mem_uIcc, hy⟩
    · exact Complex.mem_reProdIm.mpr ⟨(mem_singleton_iff.mp hx).symm ▸ right_mem_uIcc, hy⟩

/-- Taylor division with an analytic remainder centered at an arbitrary point. -/
private theorem analyticAt_taylor_quotient {f : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (n : ℕ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H p ∧ ∀ z ≠ p,
      f z / (z - p) ^ n =
        (∑ i ∈ Finset.range n,
          (iteratedDeriv i f p / (i.factorial : ℂ)) * (z - p) ^ ((i : ℤ) - n)) + H z := by
  let g : ℂ → ℂ := fun w => f (w + p)
  have hg : AnalyticAt ℂ g 0 := by
    exact hf.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + p) 0) (zero_add p)
  obtain ⟨R, hR, hTaylor⟩ := hg.exists_eventuallyEq_sum_add_pow_mul n
  have hd (i : ℕ) : iteratedDeriv i g 0 = iteratedDeriv i f p := by
    simp [g, iteratedDeriv_comp_add_const]
  let P (z : ℂ) : ℂ := ∑ i ∈ Finset.range n,
    (iteratedDeriv i f p / (i.factorial : ℂ)) * (z - p) ^ ((i : ℤ) - n)
  let H (z : ℂ) : ℂ := if z = p then R 0 else f z / (z - p) ^ n - P z
  refine ⟨H, ?_, fun z hz => by simp [H, P, hz]⟩
  have hRshift : AnalyticAt ℂ (fun z => R (z - p)) p := by
    exact hR.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - p) p) (sub_self p)
  apply hRshift.congr
  have ht : Tendsto (fun z : ℂ => z - p) (nhds p) (nhds 0) := by
    simpa using (show ContinuousAt (fun z : ℂ => z - p) p by fun_prop).tendsto
  filter_upwards [ht.eventually hTaylor] with z hz
  by_cases hz' : z = p
  · simp [hz', H]
  have hne : z - p ≠ 0 := sub_ne_zero.mpr hz'
  change R (z - p) = H z
  have hH : H z = f z / (z - p) ^ n - P z := by simp [H, hz']
  rw [hH]
  change g (z - p) = _ at hz
  simp only [g, sub_add_cancel, hd, smul_eq_mul] at hz
  rw [hz, add_div, mul_div_cancel_left₀ _ (pow_ne_zero _ hne), eq_comm, sub_eq_iff_eq_add]
  rw [add_comm, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast]
  ring

/-- Cauchy's derivative formula for a rectangle, with the pole in its interior. -/
theorem rectIntegral_cauchy {f : ℂ → ℂ} {p : ℂ} {a b c d : ℝ} (n : ℕ)
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d)
    (hf : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ f z) :
    rectIntegral (fun z => f z / (z - p) ^ (n + 1)) a b c d =
      (2 * Real.pi * I) * (iteratedDeriv n f p / (n.factorial : ℂ)) := by
  have hp : p ∈ [[a, b]] ×ℂ [[c, d]] := by
    rw [Complex.mem_reProdIm, uIcc_of_le (ha.trans hb).le, uIcc_of_le (hc.trans hd).le]
    exact ⟨⟨ha.le, hb.le⟩, ⟨hc.le, hd.le⟩⟩
  obtain ⟨R, hR, hR_eq⟩ := analyticAt_taylor_quotient (hf p hp) (n + 1)
  let L (i : ℕ) (z : ℂ) := (iteratedDeriv i f p / (i.factorial : ℂ)) *
      (z - p) ^ ((i : ℤ) - (n + 1 : ℕ))
  have hnE := point_notMem_rectEdges ha.ne hb.ne' hc.ne hd.ne'
  have hRall (z) (hz : z ∈ [[a, b]] ×ℂ [[c, d]]) : AnalyticAt ℂ R z := by
    by_cases he : z = p
    · simpa [he] using hR
    have hfQ : AnalyticAt ℂ (fun w => f w / (w - p) ^ (n + 1)) z :=
      (hf z hz).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr he))
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - p) z := by fun_prop
    have hL (i : ℕ) : AnalyticAt ℂ (L i) z :=
      analyticAt_const.fun_mul (hbase.fun_zpow (sub_ne_zero.mpr he))
    have hS := Finset.analyticAt_fun_sum (Finset.range (n + 1)) (fun i _ => hL i)
    refine (hfQ.sub hS).congr ?_
    filter_upwards [(eventually_ne_nhds he)] with w hw
    simp [hR_eq w hw, L]
  have hLc (i : ℕ) : ContinuousOn (L i) (rectEdges a b c d) :=
    continuousOn_const.mul ((show Continuous (fun z : ℂ => z - p) by fun_prop).continuousOn.zpow₀ _
      (fun z hz => Or.inl (sub_ne_zero.mpr (fun he => hnE (he ▸ hz)))))
  have hEq : EqOn (fun z => f z / (z - p) ^ (n + 1))
      (fun z => (∑ i ∈ Finset.range (n + 1), L i z) + R z) (rectEdges a b c d) :=
    fun z hz => hR_eq z (fun he => hnE (he ▸ hz))
  rw [rectIntegral_congr_edges hEq,
    rectIntegral_add (continuousOn_finsetSum _ fun i _ => hLc i)
      (fun z hz => (hRall z (rectEdges_subset hz)).continuousAt.continuousWithinAt),
    rectIntegral_eq_zero_of_differentiableOn (fun z hz => (hRall z hz).differentiableAt.differentiableWithinAt),
    add_zero, rectIntegral_sum (fun i _ => hLc i)]
  rw [Finset.sum_eq_single n]
  · unfold L
    rw [rectIntegral_const_mul]
    have he : (n : ℤ) - ((n + 1 : ℕ) : ℤ) = -1 := by omega
    simp only [he, zpow_neg_one, rectIntegral_sub_inv ha hb hc hd]
    ring
  · intro i hi hine
    unfold L
    rw [rectIntegral_const_mul,
      rectIntegral_sub_zpow_of_ne_neg_one (by omega) ha.ne hb.ne' hc.ne hd.ne', mul_zero]
  · simp


private theorem integrable_of_quadratic_decay {f : ℝ → ℂ} (hf : Continuous f)
    {C A : ℝ} (hdecay : ∀ y : ℝ, A ≤ |y| → |y| ^ 2 * ‖f y‖ ≤ C) : Integrable f := by
  let B := max 1 A
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -B) (b := B)).bddAbove_image
    (show Continuous (fun y => (1 + y ^ 2) * ‖f y‖) by fun_prop).continuousOn
  have hi : Integrable (fun y : ℝ => max M (2 * C) * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with y
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  by_cases hy : |y| ≤ B
  · exact (hM (mem_image_of_mem _ (abs_le.mp hy : y ∈ Icc (-B) B))).trans (le_max_left _ _)
  · have hya : A ≤ |y| := (le_max_right 1 A).trans (le_of_not_ge hy)
    have hy1 : 1 ≤ |y| := hB.trans (le_of_not_ge hy)
    have hl : 1 ≤ y ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have hh := hdecay y hya
    rw [sq_abs] at hh
    calc
      (1 + y ^ 2) * ‖f y‖ ≤ (2 * y ^ 2) * ‖f y‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = 2 * (y ^ 2 * ‖f y‖) := by ring
      _ ≤ max M (2 * C) := (mul_le_mul_of_nonneg_left hh (by norm_num)).trans (le_max_right _ _)

private theorem vertical_cauchy_integrable {f : ℂ → ℂ} {p : ℂ} {a : ℝ} (n : ℕ)
    (ha : a ≠ p.re) (hf : Continuous (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)))
    (hint : Integrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I))) :
    Integrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I) /
      ((a : ℂ) + (y : ℂ) * I - p) ^ (n + 1)) := by
  have hbd (y : ℝ) : |a - p.re| ≤ ‖(a : ℂ) + (y : ℂ) * I - p‖ := by
    simpa [Complex.mul_re] using abs_re_le_norm ((a : ℂ) + (y : ℂ) * I - p)
  have ha' : 0 < |a - p.re| := abs_pos.mpr (sub_ne_zero.mpr ha)
  have hcont : Continuous (fun y : ℝ => ((a : ℂ) + (y : ℂ) * I - p) ^ (n + 1)) := by fun_prop
  have hne (y : ℝ) : ((a : ℂ) + (y : ℂ) * I - p) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (norm_pos_iff.mp (ha'.trans_le (hbd y)))
  refine (hint.norm.div_const (|a - p.re| ^ (n + 1))).mono'
    (hf.div hcont hne).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    (pow_le_pow_left₀ (abs_nonneg _) (hbd y) _)

private theorem tendsto_horizontal_cauchy {ι : Type*} {l : Filter ι}
    {f : ℂ → ℂ} {p : ℂ} {a b C : ℝ} {T : ι → ℝ} (hab : a < b) (n : ℕ)
    (hT : Tendsto (fun i => |T i|) l atTop)
    (hD : ∀ᶠ i in l, ∀ x ∈ Icc a b, |T i| * ‖f ((x : ℂ) + (T i : ℂ) * I)‖ ≤ C) :
    Tendsto (fun i => ∫ x : ℝ in a..b, f ((x : ℂ) + (T i : ℂ) * I) /
      ((x : ℂ) + (T i : ℂ) * I - p) ^ (n + 1)) l (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun i => (C / |T i|) * |b - a|) l (nhds 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp hT).const_mul C).mul_const |b - a|
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [hD, hT.eventually (eventually_ge_atTop (|p.im| + 1))] with i hi hlarge
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have h1 : 1 ≤ |T i - p.im| := by linarith [abs_sub_abs_le_abs_sub (T i) p.im]
  have hnorm : 1 ≤ ‖(x : ℂ) + (T i : ℂ) * I - p‖ :=
    h1.trans (by simpa [Complex.mul_im] using abs_im_le_norm ((x : ℂ) + (T i : ℂ) * I - p))
  have hx' : x ∈ Icc a b := Ioc_subset_Icc_self (uIoc_of_le hab.le ▸ hx)
  have ht : 0 < |T i| := by linarith [abs_nonneg p.im]
  rw [norm_div, norm_pow]
  calc
    _ ≤ ‖f ((x : ℂ) + (T i : ℂ) * I)‖ / 1 :=
      div_le_div_of_nonneg_left (norm_nonneg _) one_pos (one_le_pow₀ hnorm)
    _ ≤ C / |T i| := by simpa [le_div_iff₀ ht, mul_comm] using hi x hx'

set_option maxHeartbeats 600000 in
/-- Asymptotic Cauchy formula along independently chosen upper and lower
heights. Only an inverse-height bound at the selected horizontal lines and
a quadratic tail bound on each vertical line are needed. -/
theorem asymptotic_cauchy_sparse {f : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ}
    (hab : a < b) (hf : ∀ z : ℂ, z.re ∈ Icc a b → AnalyticAt ℂ f z)
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hH : ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ Icc a b,
      |low i| * ‖f ((x : ℂ) + (low i : ℂ) * I)‖ ≤ C ∧
      |high i| * ‖f ((x : ℂ) + (high i : ℂ) * I)‖ ≤ C)
    (hV : ∀ x ∈ ({a, b} : Set ℝ), ∃ C A : ℝ, ∀ y : ℝ, A ≤ |y| →
      |y| ^ 2 * ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C)
    (p : ℂ) (n : ℕ) (ha : a ≠ p.re) (hb : b ≠ p.re) :
    let K := fun z => f z / (z - p) ^ (n + 1)
    Integrable (fun y : ℝ => K ((a : ℂ) + (y : ℂ) * I)) ∧
    Integrable (fun y : ℝ => K ((b : ℂ) + (y : ℂ) * I)) ∧
    (I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ, K ((a : ℂ) + (y : ℂ) * I))) =
      if p.re ∈ Ioo a b then
        (2 * Real.pi * I) * (iteratedDeriv n f p / (n.factorial : ℂ)) else 0 := by
  dsimp only
  let K := fun z => f z / (z - p) ^ (n + 1)
  change Integrable (fun y : ℝ => K ((a : ℂ) + (y : ℂ) * I)) ∧
    Integrable (fun y : ℝ => K ((b : ℂ) + (y : ℂ) * I)) ∧ _
  have hv (x : ℝ) (hx : x ∈ ({a, b} : Set ℝ)) (hx' : x ≠ p.re) :
      Integrable (fun y : ℝ => K ((x : ℂ) + (y : ℂ) * I)) := by
    have hmem : x ∈ Icc a b := by
      rcases (mem_insert_iff.mp hx) with rfl | h
      · exact ⟨le_rfl, hab.le⟩
      · rw [mem_singleton_iff.mp h]; exact ⟨hab.le, le_rfl⟩
    have hc : Continuous (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      have hz : (((x : ℂ) + (y : ℂ) * I)).re ∈ Icc a b := by simpa [Complex.mul_re] using hmem
      have hmap : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) y := by fun_prop
      exact ContinuousAt.comp (f := fun t : ℝ => (x : ℂ) + (t : ℂ) * I)
        (hf _ hz).continuousAt hmap
    obtain ⟨C, A, h⟩ := hV x hx
    exact vertical_cauchy_integrable n hx' hc (integrable_of_quadratic_decay hc h)
  have hA := hv a (by simp) ha
  have hB := hv b (by simp) hb
  refine ⟨hA, hB, ?_⟩
  obtain ⟨C, hH⟩ := hH
  have hL := tendsto_horizontal_cauchy (p := p) hab n (tendsto_abs_atBot_atTop.comp hlo)
    (hH.mono fun _ hi x hx => (hi x hx).1)
  have hU := tendsto_horizontal_cauchy (p := p) hab n (tendsto_abs_atTop_atTop.comp hhi)
    (hH.mono fun _ hi x hx => (hi x hx).2)
  have hrect := ((hL.sub hU).add
    ((intervalIntegral_tendsto_integral hB hlo hhi).const_mul I)).sub
      ((intervalIntegral_tendsto_integral hA hlo hhi).const_mul I)
  simp only [sub_self, zero_add] at hrect
  have hlimit : Tendsto (fun i => rectIntegral K a b (low i) (high i)) atTop
      (nhds (I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ, K ((a : ℂ) + (y : ℂ) * I)))) := by
    simpa only [rectIntegral_eq_edges, K] using hrect
  apply tendsto_nhds_unique hlimit
  apply tendsto_const_nhds.congr'
  filter_upwards [hlo.eventually (eventually_lt_atBot p.im),
    hhi.eventually (eventually_gt_atTop p.im)] with i hi₁ hi₂
  have hf' (z : ℂ) (hz : z ∈ [[a, b]] ×ℂ [[low i, high i]]) : AnalyticAt ℂ f z :=
    hf z (uIcc_of_le hab.le ▸ (Complex.mem_reProdIm.mp hz).1)
  split_ifs with hp
  · exact (rectIntegral_cauchy n hp.1 hp.2 hi₁ hi₂ hf').symm
  · symm
    apply rectIntegral_eq_zero_of_differentiableOn
    intro z hz
    have hne : z ≠ p := by
      intro he
      subst z
      have hm : p.re ∈ Icc a b := uIcc_of_le hab.le ▸ (Complex.mem_reProdIm.mp hz).1
      exact hp ⟨hm.1.lt_of_ne ha, hm.2.lt_of_ne hb.symm⟩
    have hden : AnalyticAt ℂ (fun w : ℂ => (w - p) ^ (n + 1)) z := by fun_prop
    have hk := (hf' z hz).div hden (pow_ne_zero _ (sub_ne_zero.mpr hne))
    exact hk.differentiableAt.differentiableWithinAt


/-- The two-line part of B.2.2.4, for a closed substrip of holomorphy. -/
theorem asymptotic_cauchy_strip {f : ℂ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : ∀ z : ℂ, z.re ∈ Icc a b → AnalyticAt ℂ f z)
    (hdecay : ∃ C A : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, A ≤ |y| →
      |y| ^ 2 * ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C)
    (p : ℂ) (n : ℕ) (ha : a ≠ p.re) (hb : b ≠ p.re) :
    let K := fun z => f z / (z - p) ^ (n + 1)
    Integrable (fun y : ℝ => K ((a : ℂ) + (y : ℂ) * I)) ∧
    Integrable (fun y : ℝ => K ((b : ℂ) + (y : ℂ) * I)) ∧
    (I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ, K ((a : ℂ) + (y : ℂ) * I))) =
      if p.re ∈ Ioo a b then
        (2 * Real.pi * I) * (iteratedDeriv n f p / (n.factorial : ℂ)) else 0 := by
  obtain ⟨C, A, h⟩ := hdecay
  refine asymptotic_cauchy_sparse hab hf
    (low := fun i => -(i : ℝ)) (high := fun i => (i : ℝ))
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop ?_ ?_ p n ha hb
  · refine ⟨C, ?_⟩
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max 1 A))] with i hi
    intro x hx
    have hy (y : ℝ) (hy' : |y| = (i : ℝ)) :
        |y| * ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C := by
      have h1 : 1 ≤ |y| := by rw [hy']; exact (le_max_left _ _).trans hi
      have hA : A ≤ |y| := by rw [hy']; exact (le_max_right _ _).trans hi
      refine (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans (h x hx y hA)
      simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right h1 (abs_nonneg y)
    exact ⟨hy _ (by simp), hy _ (by simp)⟩
  · intro x hx
    rcases (mem_insert_iff.mp hx) with rfl | hx
    · exact ⟨C, A, h _ ⟨le_rfl, hab.le⟩⟩
    · obtain rfl := mem_singleton_iff.mp hx
      exact ⟨C, A, h _ ⟨hab.le, le_rfl⟩⟩

set_option maxHeartbeats 600000 in
/-- The repaired one-line part of B.2.2.4. The added uniform vertical L¹
bound controls the edge that is sent to the left. -/
theorem asymptotic_cauchy_left_halfplane {f : ℂ → ℂ} {b M : ℝ}
    (hf : ∀ z : ℂ, z.re ≤ b → AnalyticAt ℂ f z)
    (hdecay : ∃ C A : ℝ, ∀ x ≤ b, ∀ y : ℝ, A ≤ |y| →
      |y| ^ 2 * ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C)
    (hL : ∀ x ≤ b, (∫ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖) ≤ M)
    (p : ℂ) (n : ℕ) (hp : b ≠ p.re) :
    let K := fun z => f z / (z - p) ^ (n + 1)
    Integrable (fun y : ℝ => K ((b : ℂ) + (y : ℂ) * I)) ∧
    I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)) =
      if p.re < b then
        (2 * Real.pi * I) * (iteratedDeriv n f p / (n.factorial : ℂ)) else 0 := by
  dsimp only
  let K := fun z => f z / (z - p) ^ (n + 1)
  let a (j : ℕ) := min b p.re - ((j : ℝ) + 1)
  have hdist (j : ℕ) : (j : ℝ) + 1 ≤ p.re - a j := by
    dsimp [a]
    linarith [min_le_right b p.re]
  have hab (j : ℕ) : a j < b := by
    dsimp [a]
    linarith [min_le_left b p.re, Nat.cast_nonneg (α := ℝ) j]
  have hap (j : ℕ) : a j < p.re := by linarith [hdist j, Nat.cast_nonneg (α := ℝ) j]
  obtain ⟨C, A, hD⟩ := hdecay
  have hstrip (j : ℕ) := asymptotic_cauchy_strip (hab j)
    (fun z hz => hf z hz.2) ⟨C, A, fun x hx => hD x hx.2⟩ p n (hap j).ne hp
  refine ⟨(hstrip 0).2.1, ?_⟩
  have hleft : Tendsto (fun j => ∫ y : ℝ, K ((a j : ℂ) + (y : ℂ) * I)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hLim : Tendsto (fun j : ℕ => M / ((j : ℝ) + 1)) atTop (nhds 0) := by
      have ht := tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      simpa [div_eq_mul_inv, Function.comp_def] using (tendsto_inv_atTop_zero.comp ht).const_mul M
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hLim
    refine Eventually.of_forall fun j => ?_
    have h1 : 0 < (j : ℝ) + 1 := by positivity
    have hline : Continuous (fun y : ℝ => f ((a j : ℂ) + (y : ℂ) * I)) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have hmap : ContinuousAt (fun t : ℝ => (a j : ℂ) + (t : ℂ) * I) y := by fun_prop
      have hx : (((a j : ℂ) + (y : ℂ) * I)).re ≤ b := by
        simpa [Complex.mul_re] using (hab j).le
      exact ContinuousAt.comp (f := fun t : ℝ => (a j : ℂ) + (t : ℂ) * I)
        (hf _ hx).continuousAt hmap
    have hint := integrable_of_quadratic_decay hline (hD (a j) (hab j).le)
    refine (norm_integral_le_integral_norm _).trans ?_
    calc
      _ ≤ ∫ y : ℝ, ‖f ((a j : ℂ) + (y : ℂ) * I)‖ / ((j : ℝ) + 1) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hint.norm.div_const _)
        refine Eventually.of_forall fun y => ?_
        have hn : (j : ℝ) + 1 ≤ ‖(a j : ℂ) + (y : ℂ) * I - p‖ := by
          refine (hdist j).trans ?_
          simpa [Complex.mul_re, abs_of_neg (sub_neg.mpr (hap j)), neg_sub] using
            abs_re_le_norm ((a j : ℂ) + (y : ℂ) * I - p)
        have hn1 : 1 ≤ ‖(a j : ℂ) + (y : ℂ) * I - p‖ := by
          linarith [Nat.cast_nonneg (α := ℝ) j]
        simp only [K, norm_div, norm_pow]
        apply div_le_div_of_nonneg_left (norm_nonneg _) h1
        rw [pow_succ]
        exact hn.trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hn1))
      _ ≤ _ := by rw [integral_div]; exact div_le_div_of_nonneg_right (hL _ (hab j).le) h1.le
  let limit := if p.re < b then
    (2 * Real.pi * I) * (iteratedDeriv n f p / (n.factorial : ℂ)) else 0
  have hconst (j : ℕ) :
      I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ, K ((a j : ℂ) + (y : ℂ) * I)) = limit := by
    simpa [K, limit, mem_Ioo, (hap j)] using (hstrip j).2.2
  have ht : Tendsto (fun j =>
      I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ, K ((a j : ℂ) + (y : ℂ) * I))) atTop
      (nhds (I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)))) := by
    simpa only [mul_zero, sub_zero] using
      (hleft.const_mul I).const_sub (I * (∫ y : ℝ, K ((b : ℂ) + (y : ℂ) * I)))
  exact tendsto_nhds_unique ht
    (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hconst j).symm))


/-- A pole of order `n + 1` contributes the order-`n` Taylor coefficient
of the analytic numerator after multiplication by the test function. -/
theorem rectIntegral_pole_product {g Φ : ℂ → ℂ} {p : ℂ} {a b c d : ℝ} (n : ℕ)
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d)
    (hg : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ g z)
    (hΦ : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ Φ z) :
    rectIntegral (fun z => Φ z * (g z / (z - p) ^ (n + 1))) a b c d =
      (2 * Real.pi * I) * (iteratedDeriv n (fun z => Φ z * g z) p / (n.factorial : ℂ)) := by
  simpa only [mul_div_assoc] using
    rectIntegral_cauchy n ha hb hc hd (fun z hz => (hΦ z hz).fun_mul (hg z hz))

/-- The manuscript's factorization of the residue fails for a double pole,
even with the entire, vertically rapidly decreasing test `z * exp(z²)`. -/
theorem rectIntegral_printed_double_pole_obstruction :
    rectIntegral (fun z => (z * Complex.exp (z ^ 2)) * (1 / z ^ 2)) (-1) 1 (-1) 1 ≠
      ((0 : ℂ) * Complex.exp 0) * rectIntegral (fun z => 1 / z ^ 2) (-1) 1 (-1) 1 := by
  have hΦ : ∀ z : ℂ, AnalyticAt ℂ (fun w => w * Complex.exp (w ^ 2)) z := by
    intro z
    fun_prop
  have hres := rectIntegral_pole_product
    (g := fun _ => (1 : ℂ)) (Φ := fun z => z * Complex.exp (z ^ 2)) (p := 0)
    (a := -1) (b := 1) (c := -1) (d := 1) 1
    (by simp) (by simp) (by simp) (by simp) (fun _ _ => analyticAt_const) (fun z _ => hΦ z)
  have hd : deriv (fun z : ℂ => z * Complex.exp (z ^ 2)) 0 = 1 := by
    have hE : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2)) 0 := by fun_prop
    change deriv (fun z : ℂ => id z * Complex.exp (z ^ 2)) 0 = 1
    rw [deriv_fun_mul differentiableAt_id hE]
    simp
  simp [iteratedDeriv_one, hd] at hres
  simp only [one_div]
  rw [hres]
  simp


/-- A finite principal part. Index `j` is the coefficient of the Laurent
power `-(j+1)`, so index zero gives the residue. -/
structure PrincipalPart where
  center : ℂ
  length : ℕ
  coeff : ℕ → ℂ

noncomputable def PrincipalPart.eval (P : PrincipalPart) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (P.length + 1), P.coeff j * (z - P.center) ^ (-((j : ℤ) + 1))

private theorem PrincipalPart.continuousOn_eval {P : PrincipalPart} {s : Set ℂ}
    (hs : P.center ∉ s) : ContinuousOn P.eval s := by
  apply continuousOn_finsetSum
  intro j _
  apply continuousOn_const.mul
  have hc : Continuous (fun z : ℂ => z - P.center) := by fun_prop
  exact hc.continuousOn.zpow₀ _ (fun z hz => Or.inl (sub_ne_zero.mpr (fun h => hs (h ▸ hz))))

theorem PrincipalPart.rectIntegral_eval {P : PrincipalPart} {a b c d : ℝ}
    (ha : a < P.center.re) (hb : P.center.re < b)
    (hc : c < P.center.im) (hd : P.center.im < d) :
    rectIntegral P.eval a b c d = (2 * Real.pi * I) * P.coeff 0 := by
  have hE := point_notMem_rectEdges ha.ne hb.ne' hc.ne hd.ne'
  unfold PrincipalPart.eval
  rw [rectIntegral_sum]
  · rw [Finset.sum_eq_single 0]
    · rw [rectIntegral_const_mul]
      simp only [Nat.cast_zero, zero_add, zpow_neg_one, rectIntegral_sub_inv ha hb hc hd]
      ring
    · intro j hj hne
      rw [rectIntegral_const_mul, rectIntegral_sub_zpow_of_ne_neg_one (by omega)
        ha.ne hb.ne' hc.ne hd.ne', mul_zero]
    · simp
  · intro j _
    apply continuousOn_const.mul
    have hs : Continuous (fun z : ℂ => z - P.center) := by fun_prop
    exact hs.continuousOn.zpow₀ _ (fun z hz => Or.inl (sub_ne_zero.mpr (fun h => hE (h ▸ hz))))

/-- The finite rectangular residue formula from the principal parts and the
holomorphic remainder. Each residue is taken after multiplying the original
meromorphic function by the test function. -/
theorem rectIntegral_eq_sum_principalResidues {ι : Type*} {s : Finset ι}
    {f g : ℂ → ℂ} {P : ι → PrincipalPart} {a b c d : ℝ}
    (hg : DifferentiableOn ℂ g ([[a, b]] ×ℂ [[c, d]]))
    (hint : ∀ i ∈ s, (P i).center.re ∈ Ioo a b ∧ (P i).center.im ∈ Ioo c d)
    (hdecomp : EqOn f (fun z => g z + ∑ i ∈ s, (P i).eval z) (rectEdges a b c d)) :
    rectIntegral f a b c d = (2 * Real.pi * I) * ∑ i ∈ s, (P i).coeff 0 := by
  have hcont (i : ι) (hi : i ∈ s) : ContinuousOn (P i).eval (rectEdges a b c d) := by
    obtain ⟨hne, hni⟩ := hint i hi
    exact PrincipalPart.continuousOn_eval (point_notMem_rectEdges hne.1.ne hne.2.ne' hni.1.ne hni.2.ne')
  rw [rectIntegral_congr_edges hdecomp, rectIntegral_add (hg.continuousOn.mono rectEdges_subset)
    (continuousOn_finsetSum _ hcont), rectIntegral_eq_zero_of_differentiableOn hg,
    zero_add, rectIntegral_sum hcont, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  obtain ⟨hx, hy⟩ := hint i hi
  exact PrincipalPart.rectIntegral_eval hx.1 hx.2 hy.1 hy.2


/-- A principal part represents a meromorphic function near its center
when the difference has an analytic extension across the center. -/
def PrincipalPart.Represents (P : PrincipalPart) (f : ℂ → ℂ) : Prop :=
  ∃ R : ℂ → ℂ, AnalyticAt ℂ R P.center ∧
    ∀ᶠ z in nhdsWithin P.center {P.center}ᶜ, f z = P.eval z + R z

private noncomputable def principalPartOfNumerator (g : ℂ → ℂ) (p : ℂ) (n : ℕ) : PrincipalPart :=
  ⟨p, n, fun j => iteratedDeriv (n - j) g p / ((n - j).factorial : ℂ)⟩

private theorem principalPartOfNumerator_represents {g : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g p) :
    (principalPartOfNumerator g p n).Represents (fun z => g z / (z - p) ^ (n + 1)) := by
  obtain ⟨R, hR, hTaylor⟩ := analyticAt_taylor_quotient hg (n + 1)
  refine ⟨R, hR, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have ht := hTaylor z (show z ≠ p from hz)
  change g z / (z - p) ^ (n + 1) = (principalPartOfNumerator g p n).eval z + R z
  rw [ht]
  congr 1
  unfold PrincipalPart.eval principalPartOfNumerator
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by
    have := Finset.mem_range.mp hj
    omega
  rw [show n + 1 - 1 - j = n - j by omega]
  congr 1
  push_cast [Nat.cast_sub hj']
  congr 1
  omega

private theorem exists_principalPart_at_pole {f : ℂ → ℂ} {p : ℂ}
    (hp : meromorphicOrderAt f p < 0) :
    ∃ P : PrincipalPart, P.center = p ∧ P.Represents f := by
  have hf := meromorphicAt_of_meromorphicOrderAt_ne_zero hp.ne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp.ne_top
  have hm' : m < 0 := by simpa [← hm] using hp
  obtain ⟨g, hg, -, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hm.symm
  let n := (-m - 1).toNat
  have hn : m = -((n : ℤ) + 1) := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  let P := principalPartOfNumerator g p n
  obtain ⟨R, hR, hlocal⟩ := principalPartOfNumerator_represents (n := n) hg
  refine ⟨P, rfl, R, hR, ?_⟩
  filter_upwards [heq, hlocal] with z hz hRz
  rw [hz, hn, smul_eq_mul, ← Int.natCast_succ, zpow_neg, zpow_natCast,
    ← div_eq_inv_mul]
  exact hRz

/-- The principal part at a pole. Points of nonnegative order have the zero
principal part. Its coefficients are those of the convergent Laurent expansion. -/
noncomputable def principalPartAt (f : ℂ → ℂ) (p : ℂ) : PrincipalPart :=
  if h : meromorphicOrderAt f p < 0 then (exists_principalPart_at_pole h).choose
  else ⟨p, 0, 0⟩

@[simp]
theorem principalPartAt_center (f : ℂ → ℂ) (p : ℂ) : (principalPartAt f p).center = p := by
  unfold principalPartAt
  split
  · exact (exists_principalPart_at_pole ‹_›).choose_spec.1
  · rfl

theorem principalPartAt_represents {f : ℂ → ℂ} {p : ℂ} (hp : meromorphicOrderAt f p < 0) :
    (principalPartAt f p).Represents f := by
  rw [principalPartAt, dite_eq_left hp]
  exact (exists_principalPart_at_pole hp).choose_spec.2

/-- The residue, given by the coefficient of Laurent degree minus one. -/
noncomputable def meromorphicResidue (f : ℂ → ℂ) (p : ℂ) : ℂ :=
  (principalPartAt f p).coeff 0

/-- Poles in a compact subset of a meromorphic function's domain are finite. -/
theorem poles_finite_on_compact {f : ℂ → ℂ} {S : Set ℂ}
    (hS : IsCompact S) (hf : MeromorphicOn f S) :
    {z ∈ S | meromorphicOrderAt f z < 0}.Finite := by
  refine ((MeromorphicOn.divisor f S).finiteSupport hS).subset ?_
  intro z hz
  rw [Function.mem_support, hf.divisor_apply hz.1]
  have ho : meromorphicOrderAt f z < 0 := hz.2
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  rw [← hm, WithTop.untop₀_coe]
  intro h
  simp [← hm, h] at ho

private theorem PrincipalPart.analyticAt_eval {P : PrincipalPart} {z : ℂ}
    (hz : z ≠ P.center) : AnalyticAt ℂ P.eval z := by
  apply Finset.analyticAt_fun_sum
  intro j _
  have h : AnalyticAt ℂ (fun w : ℂ => w - P.center) z := by fun_prop
  exact analyticAt_const.fun_mul (h.fun_zpow (sub_ne_zero.mpr hz))

/-- Subtract the principal parts at the poles in a compact region to obtain
an analytic remainder. The function is taken in meromorphic normal form,
so its values at regular points are the analytic values. -/
theorem exists_principalPart_remainder {f : ℂ → ℂ} {S : Set ℂ}
    (hf : MeromorphicNFOn f S) {s : Finset ℂ}
    (hs : ∀ z : ℂ, z ∈ s ↔ z ∈ S ∧ meromorphicOrderAt f z < 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g S ∧
      EqOn f (fun z => g z + ∑ q ∈ s, (principalPartAt f q).eval z) (S \ (s : Set ℂ)) := by
  classical
  let P := principalPartAt f
  have hloc (p : ℂ) (hp : p ∈ s) : ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧
      ∀ᶠ z in nhdsWithin p {p}ᶜ, f z = (P p).eval z + R z := by
    simpa only [PrincipalPart.Represents, P, principalPartAt_center] using
      principalPartAt_represents (hs p |>.mp hp).2
  let R (p : ℂ) (hp : p ∈ s) := (hloc p hp).choose
  let G (z : ℂ) : ℂ := if hz : z ∈ s then R z hz z - ∑ q ∈ s.erase z, (P q).eval z
    else f z - ∑ q ∈ s, (P q).eval z
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    by_cases hps : p ∈ s
    · have hR : AnalyticAt ℂ (R p hps) p := (hloc p hps).choose_spec.1
      have ha (q : ℂ) (hq : q ∈ s.erase p) : AnalyticAt ℂ (P q).eval p :=
        PrincipalPart.analyticAt_eval (by simpa only [P, principalPartAt_center] using
          (Finset.mem_erase.mp hq).1.symm)
      have hA := hR.fun_sub (Finset.analyticAt_fun_sum (s.erase p) ha)
      apply hA.congr
      have hE := (hloc p hps).choose_spec.2
      rw [eventually_nhdsWithin_iff] at hE
      have hAvoid : ∀ᶠ w in nhds p, ∀ q ∈ s.erase p, w ≠ q :=
        (eventually_all_finset _).mpr fun q hq => eventually_ne_nhds (Finset.mem_erase.mp hq).1.symm
      filter_upwards [hE, hAvoid] with w hw hwa
      by_cases he : w = p
      · subst w
        simp [G, hps]
      have hwn : w ∉ s := fun hws => hwa w (Finset.mem_erase.mpr ⟨he, hws⟩) rfl
      have hs' := Finset.sum_erase_add (s := s) (f := fun q => (P q).eval w) hps
      have hf' := hw (show w ∈ ({p} : Set ℂ)ᶜ from he)
      change f w = (P p).eval w + R p hps w at hf'
      dsimp only [G]
      rw [dite_eq_right hwn, ← hs', hf']
      ring
    · have hfp : AnalyticAt ℂ f p := (hf hp).meromorphicOrderAt_nonneg_iff_analyticAt.mp
        (le_of_not_gt (fun h => hps ((hs p).mpr ⟨hp, h⟩)))
      have ha (q : ℂ) (hq : q ∈ s) : AnalyticAt ℂ (P q).eval p :=
        PrincipalPart.analyticAt_eval (by simpa only [P, principalPartAt_center] using
          (fun h : p = q => hps (h ▸ hq)))
      apply (hfp.fun_sub (Finset.analyticAt_fun_sum s ha)).congr
      have hAvoid : ∀ᶠ w in nhds p, ∀ q ∈ s, w ≠ q :=
        (eventually_all_finset _).mpr fun q hq => eventually_ne_nhds (fun he => hps (he ▸ hq))
      filter_upwards [hAvoid] with w hwa
      have hwn : w ∉ s := fun hws => hwa w hws rfl
      simp [G, hwn]
  · intro z hz
    have hn : z ∉ s := hz.2
    simp [G, P, hn]


/-- The poles of `f` in the closed rectangle. For a contour free of poles,
these are exactly the poles of the open rectangle. -/
noncomputable def rectanglePoles (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : MeromorphicOn f ([[a, b]] ×ℂ [[c, d]])) : Finset ℂ :=
  (poles_finite_on_compact (isCompact_uIcc.reProdIm isCompact_uIcc) hf).toFinset

@[simp]
theorem mem_rectanglePoles {f : ℂ → ℂ} {a b c d : ℝ}
    {hf : MeromorphicOn f ([[a, b]] ×ℂ [[c, d]])} {z : ℂ} :
    z ∈ rectanglePoles f a b c d hf ↔
      z ∈ [[a, b]] ×ℂ [[c, d]] ∧ meromorphicOrderAt f z < 0 :=
  Set.Finite.mem_toFinset _

private theorem rectanglePoles_interior {f : ℂ → ℂ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hf : MeromorphicOn f ([[a, b]] ×ℂ [[c, d]]))
    (he : AnalyticOnNhd ℂ f (rectEdges a b c d)) {p : ℂ}
    (hp : p ∈ rectanglePoles f a b c d hf) :
    p.re ∈ Ioo a b ∧ p.im ∈ Ioo c d := by
  obtain ⟨hp, ho⟩ := mem_rectanglePoles.mp hp
  obtain ⟨hx, hy⟩ := Complex.mem_reProdIm.mp hp
  have hn : p ∉ rectEdges a b c d := fun he' =>
    (not_lt_of_ge (he p he').meromorphicOrderAt_nonneg) ho
  have hbx : p.re ∉ ({a, b} : Set ℝ) := fun hh =>
    hn (Or.inr (Complex.mem_reProdIm.mpr ⟨hh, hy⟩))
  have hby : p.im ∉ ({c, d} : Set ℝ) := fun hh =>
    hn (Or.inl (Complex.mem_reProdIm.mpr ⟨hx, hh⟩))
  rw [uIcc_of_le hab.le] at hx
  rw [uIcc_of_le hcd.le] at hy
  refine ⟨⟨hx.1.lt_of_ne ?_, hx.2.lt_of_ne ?_⟩, ⟨hy.1.lt_of_ne ?_, hy.2.lt_of_ne ?_⟩⟩
  · exact fun h => hbx (by simp [h.symm])
  · exact fun h => hbx (by simp [h])
  · exact fun h => hby (by simp [h.symm])
  · exact fun h => hby (by simp [h])

/-- Residue theorem for a finite rectangle and a meromorphic function in
normal form, with a contour free of singularities. -/
theorem rectIntegral_meromorphic {f : ℂ → ℂ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hf : MeromorphicNFOn f ([[a, b]] ×ℂ [[c, d]]))
    (he : AnalyticOnNhd ℂ f (rectEdges a b c d)) :
    rectIntegral f a b c d = (2 * Real.pi * I) *
      ∑ p ∈ rectanglePoles f a b c d hf.meromorphicOn, meromorphicResidue f p := by
  let s := rectanglePoles f a b c d hf.meromorphicOn
  obtain ⟨g, hg, hdecomp⟩ := exists_principalPart_remainder hf (s := s)
    (fun z => mem_rectanglePoles)
  have hint (p : ℂ) (hp : p ∈ s) : p.re ∈ Ioo a b ∧ p.im ∈ Ioo c d :=
    rectanglePoles_interior hab hcd hf.meromorphicOn he hp
  exact rectIntegral_eq_sum_principalResidues (P := principalPartAt f) hg.differentiableOn
    (by simpa only [principalPartAt_center] using hint)
    (fun z hz => hdecomp ⟨rectEdges_subset hz, fun hp =>
      (not_lt_of_ge (he z hz).meromorphicOrderAt_nonneg) (mem_rectanglePoles.mp hp).2⟩)


private theorem tendsto_horizontal_integral {F : ℂ → ℂ} {a b C : ℝ} {t : ℕ → ℝ}
    (hab : a < b) (ht : Tendsto (fun j => |t j|) atTop atTop)
    (hDecay : ∀ᶠ j in atTop, ∀ x ∈ Icc a b, |t j| * ‖F ((x : ℂ) + (t j : ℂ) * I)‖ ≤ C) :
    Tendsto (fun j => ∫ x : ℝ in a..b, F ((x : ℂ) + (t j : ℂ) * I)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : Tendsto (fun j => (C / |t j|) * |b - a|) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp ht).const_mul C).mul_const |b - a|
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hb
  filter_upwards [hDecay, ht.eventually (eventually_gt_atTop 0)] with j hj htj
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  exact (le_div_iff₀ htj).mpr (by
    rw [mul_comm]
    exact hj x (Ioc_subset_Icc_self (uIoc_of_le hab.le ▸ hx)))

private theorem rectangle_in_strip {a b c d : ℝ} (hab : a < b) :
    [[a, b]] ×ℂ [[c, d]] ⊆ Complex.re ⁻¹' Icc a b :=
  fun _ hz => uIcc_of_le hab.le ▸ (Complex.mem_reProdIm.mp hz).1

theorem analyticOnNhd_rectEdges_of_lines {F : ℂ → ℂ} {a b c d : ℝ} (hab : a < b)
    (hHor : ∀ x ∈ Icc a b, AnalyticAt ℂ F ((x : ℂ) + (c : ℂ) * I) ∧
      AnalyticAt ℂ F ((x : ℂ) + (d : ℂ) * I))
    (hVert : ∀ y : ℝ, AnalyticAt ℂ F ((a : ℂ) + (y : ℂ) * I) ∧
      AnalyticAt ℂ F ((b : ℂ) + (y : ℂ) * I)) :
    AnalyticOnNhd ℂ F (rectEdges a b c d) := by
  rintro z (hz | hz)
  · have hx := hHor z.re (uIcc_of_le hab.le ▸ (Complex.mem_reProdIm.mp hz).1)
    have hy := (Complex.mem_reProdIm.mp hz).2
    rcases mem_insert_iff.mp hy with he | he
    · simpa only [← he, Complex.re_add_im] using hx.1
    · have hd : z.im = d := mem_singleton_iff.mp he
      simpa only [← hd, Complex.re_add_im] using hx.2
  · have hx := (Complex.mem_reProdIm.mp hz).1
    rcases mem_insert_iff.mp hx with he | he
    · simpa only [← he, Complex.re_add_im] using (hVert z.im).1
    · have hb : z.re = b := mem_singleton_iff.mp he
      simpa only [← hb, Complex.re_add_im] using (hVert z.im).2

/-- Shift the vertical contour when both vertical traces are integrable.
The horizontal bounds are imposed on the selected heights. -/
theorem asymptotic_residue_of_integrable {F : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ}
    (hab : a < b) (hF : MeromorphicNFOn F (Complex.re ⁻¹' Icc a b))
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hHorizontal : ∃ C : ℝ, ∀ᶠ j in atTop, ∀ x ∈ Icc a b,
      (AnalyticAt ℂ F ((x : ℂ) + (low j : ℂ) * I) ∧
        AnalyticAt ℂ F ((x : ℂ) + (high j : ℂ) * I)) ∧
      (|low j| * ‖F ((x : ℂ) + (low j : ℂ) * I)‖ ≤ C ∧
        |high j| * ‖F ((x : ℂ) + (high j : ℂ) * I)‖ ≤ C))
    (hVertical : ∀ y : ℝ, AnalyticAt ℂ F ((a : ℂ) + (y : ℂ) * I) ∧
      AnalyticAt ℂ F ((b : ℂ) + (y : ℂ) * I))
    (ha : Integrable (fun y : ℝ => F ((a : ℂ) + (y : ℂ) * I)))
    (hb : Integrable (fun y : ℝ => F ((b : ℂ) + (y : ℂ) * I))) :
    let L := fun x : ℝ => ∫ y : ℝ, F ((x : ℂ) + (y : ℂ) * I)
    Tendsto (fun j => ∑ p ∈ rectanglePoles F a b (low j) (high j)
      (fun z hz => hF.meromorphicOn z (rectangle_in_strip hab hz)), meromorphicResidue F p)
      atTop (nhds ((I * L b - I * L a) / (2 * Real.pi * I))) := by
  dsimp only
  obtain ⟨C, hH⟩ := hHorizontal
  have hl := tendsto_horizontal_integral hab (tendsto_abs_atBot_atTop.comp hlo)
    (hH.mono fun _ hj x hx => (hj x hx).2.1)
  have hu := tendsto_horizontal_integral hab (tendsto_abs_atTop_atTop.comp hhi)
    (hH.mono fun _ hj x hx => (hj x hx).2.2)
  have hrect := ((hl.sub hu).add
    ((intervalIntegral_tendsto_integral hb hlo hhi).const_mul I)).sub
      ((intervalIntegral_tendsto_integral ha hlo hhi).const_mul I)
  simp only [sub_self, zero_add] at hrect
  have hnorm := hrect.div_const (2 * (Real.pi : ℂ) * I)
  apply hnorm.congr'
  filter_upwards [hH, hlo.eventually (eventually_lt_atBot 0),
    hhi.eventually (eventually_gt_atTop 0)] with j hj hlj hhj
  have he : AnalyticOnNhd ℂ F (rectEdges a b (low j) (high j)) :=
    analyticOnNhd_rectEdges_of_lines hab (fun x hx => (hj x hx).1)
      hVertical
  have hR := rectIntegral_meromorphic hab (hlj.trans hhj) (fun {z} hz => hF (rectangle_in_strip hab hz)) he
  rw [← rectIntegral_eq_edges, hR, mul_comm, mul_div_cancel_right₀ _ Complex.two_pi_I_ne_zero]

/-- The asymptotic residue formula for the meromorphic product in normal
form. The decay bounds are imposed on the actual integration lines, and
one sums residues of the product, including all orders of the poles. -/
theorem asymptotic_residue {F : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ}
    (hab : a < b) (hF : MeromorphicNFOn F (Complex.re ⁻¹' Icc a b))
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hHorizontal : ∃ C : ℝ, ∀ᶠ j in atTop, ∀ x ∈ Icc a b,
      (AnalyticAt ℂ F ((x : ℂ) + (low j : ℂ) * I) ∧
        AnalyticAt ℂ F ((x : ℂ) + (high j : ℂ) * I)) ∧
      (|low j| * ‖F ((x : ℂ) + (low j : ℂ) * I)‖ ≤ C ∧
        |high j| * ‖F ((x : ℂ) + (high j : ℂ) * I)‖ ≤ C))
    (hVertical : ∀ x ∈ ({a, b} : Set ℝ),
      (∀ y : ℝ, AnalyticAt ℂ F ((x : ℂ) + (y : ℂ) * I)) ∧
      ∃ C A : ℝ, ∀ y : ℝ, A ≤ |y| → |y| ^ 2 * ‖F ((x : ℂ) + (y : ℂ) * I)‖ ≤ C) :
    let L := fun x : ℝ => ∫ y : ℝ, F ((x : ℂ) + (y : ℂ) * I)
    Integrable (fun y : ℝ => F ((a : ℂ) + (y : ℂ) * I)) ∧
    Integrable (fun y : ℝ => F ((b : ℂ) + (y : ℂ) * I)) ∧
    Tendsto (fun j => ∑ p ∈ rectanglePoles F a b (low j) (high j)
      (fun z hz => hF.meromorphicOn z (rectangle_in_strip hab hz)), meromorphicResidue F p)
      atTop (nhds ((I * L b - I * L a) / (2 * Real.pi * I))) := by
  dsimp only
  have hv (x : ℝ) (hx : x ∈ ({a, b} : Set ℝ)) :
      Integrable (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * I)) := by
    obtain ⟨ha, C, A, hd⟩ := hVertical x hx
    apply integrable_of_quadratic_decay _ hd
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact ContinuousAt.comp' (f := fun t : ℝ => (x : ℂ) + (t : ℂ) * I)
      (ha y).continuousAt (by fun_prop)
  have ha := hv a (by simp)
  have hb := hv b (by simp)
  exact ⟨ha, hb, asymptotic_residue_of_integrable hab hF hlo hhi hHorizontal
    (fun y => ⟨(hVertical a (by simp)).1 y, (hVertical b (by simp)).1 y⟩) ha hb⟩


private theorem closed_small_rectangle_mem_nhds {p : ℂ} {S : Set ℂ} (hS : S ∈ nhds p) :
    ∃ e : ℝ, 0 < e ∧
      ([[p.re - e, p.re + e]] ×ℂ [[p.im - e, p.im + e]]) ⊆ S := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hS
  let e := r / 3
  have he : 0 < e := by dsimp [e]; positivity
  refine ⟨e, he, fun z hz => hball ?_⟩
  obtain ⟨hx, hy⟩ := Complex.mem_reProdIm.mp hz
  rw [uIcc_of_le (by linarith : p.re - e ≤ p.re + e)] at hx
  rw [uIcc_of_le (by linarith : p.im - e ≤ p.im + e)] at hy
  have hxr : |(z - p).re| ≤ e := by
    rw [sub_re, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyi : |(z - p).im| ≤ e := by
    rw [sub_im, abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hn : ‖z - p‖ ≤ |(z - p).re| + |(z - p).im| := by
    conv_lhs => rw [← Complex.re_add_im (z - p)]
    simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le ((z - p).re : ℂ) (((z - p).im : ℂ) * I)
  rw [Metric.mem_ball, dist_eq_norm]
  exact hn.trans_lt (by dsimp [e] at *; linarith)

/-- The residue is independent of the chosen analytic remainder and of the
function's assigned value at the pole. -/
theorem PrincipalPart.residue_eq_of_eventuallyEq {P Q : PrincipalPart} {f g : ℂ → ℂ}
    (hc : P.center = Q.center) (hfg : f =ᶠ[nhdsWithin P.center {P.center}ᶜ] g)
    (hP : P.Represents f) (hQ : Q.Represents g) : P.coeff 0 = Q.coeff 0 := by
  let p := P.center
  obtain ⟨R, hR, hr⟩ := hP
  obtain ⟨S, hS, hs⟩ := hQ
  have hS' : AnalyticAt ℂ S p := by simpa only [p, hc] using hS
  have hs' : ∀ᶠ z in nhdsWithin p {p}ᶜ, g z = Q.eval z + S z := by simpa only [p, hc] using hs
  have hlocal : ∀ᶠ z in nhds p,
      (z ≠ p → f z = g z ∧ f z = P.eval z + R z ∧ g z = Q.eval z + S z) ∧
      AnalyticAt ℂ R z ∧ AnalyticAt ℂ S z := by
    have h := hfg.and (hr.and hs')
    rw [eventually_nhdsWithin_iff] at h
    exact h.and (hR.eventually_analyticAt.and hS'.eventually_analyticAt)
  obtain ⟨e, he, hrect⟩ := closed_small_rectangle_mem_nhds hlocal
  let a := p.re - e
  let b := p.re + e
  let c := p.im - e
  let d := p.im + e
  have ha : a < p.re := by dsimp [a]; linarith
  have hb : p.re < b := by dsimp [b]; linarith
  have hcc : c < p.im := by dsimp [c]; linarith
  have hd : p.im < d := by dsimp [d]; linarith
  have hne : p ∉ rectEdges a b c d := point_notMem_rectEdges ha.ne hb.ne' hcc.ne hd.ne'
  have hOn (z : ℂ) (hz : z ∈ rectEdges a b c d) :
      f z = g z ∧ f z = P.eval z + R z ∧ g z = Q.eval z + S z :=
    (hrect (rectEdges_subset hz)).1 (fun h => hne (h ▸ hz))
  have hrd : DifferentiableOn ℂ R ([[a, b]] ×ℂ [[c, d]]) :=
    fun z hz => (hrect hz).2.1.differentiableAt.differentiableWithinAt
  have hsd : DifferentiableOn ℂ S ([[a, b]] ×ℂ [[c, d]]) :=
    fun z hz => (hrect hz).2.2.differentiableAt.differentiableWithinAt
  have hcalcP := rectIntegral_eq_sum_principalResidues (s := {()}) (P := fun _ => P) hrd
    (fun _ _ => ⟨⟨ha, hb⟩, ⟨hcc, hd⟩⟩)
    (show EqOn f _ (rectEdges a b c d) from fun z hz => by
      simpa [add_comm] using (hOn z hz).2.1)
  have hcalcQ := rectIntegral_eq_sum_principalResidues (s := {()}) (P := fun _ => Q) hsd
    (fun _ _ => by simpa [← hc] using
      (show p.re ∈ Ioo a b ∧ p.im ∈ Ioo c d from ⟨⟨ha, hb⟩, ⟨hcc, hd⟩⟩))
    (show EqOn g _ (rectEdges a b c d) from fun z hz => by
      simpa [add_comm] using (hOn z hz).2.2)
  have h := rectIntegral_congr_edges (fun z hz => (hOn z hz).1)
  simp only [Finset.sum_singleton] at hcalcP hcalcQ
  rw [hcalcP, hcalcQ] at h
  exact mul_left_cancel₀ Complex.two_pi_I_ne_zero h

theorem meromorphicResidue_congr {f g : ℂ → ℂ} {p : ℂ}
    (hfg : f =ᶠ[nhdsWithin p {p}ᶜ] g) :
    meromorphicResidue f p = meromorphicResidue g p := by
  have horders := meromorphicOrderAt_congr hfg
  by_cases hf : meromorphicOrderAt f p < 0
  · have hg : meromorphicOrderAt g p < 0 := horders ▸ hf
    exact PrincipalPart.residue_eq_of_eventuallyEq
      (by simp) (by simpa using hfg)
      (principalPartAt_represents hf) (principalPartAt_represents hg)
  · have hg : ¬meromorphicOrderAt g p < 0 := horders ▸ hf
    simp [meromorphicResidue, principalPartAt, hf, hg]


/-- The residue of an analytic numerator divided by the centered coordinate
is its value at the center, including when the singularity cancels. -/
theorem meromorphicResidue_div_sub {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) :
    meromorphicResidue (fun z => g z / (z - p)) p = g p := by
  let f := fun z => g z / (z - p)
  let P : PrincipalPart := ⟨p, 0, fun _ => g p⟩
  obtain ⟨R, hR, hTaylor⟩ := analyticAt_taylor_quotient hg 1
  have hP : P.Represents f := by
    refine ⟨R, hR, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa [f, P, PrincipalPart.eval, div_eq_mul_inv] using hTaylor z hz
  by_cases hp : meromorphicOrderAt f p < 0
  · exact PrincipalPart.residue_eq_of_eventuallyEq (by simp [P])
      Filter.EventuallyEq.rfl (principalPartAt_represents hp) hP
  · have hz : g p = 0 := by
      by_contra hn
      have hline : AnalyticAt ℂ (fun z => z - p) p := by fun_prop
      have hm : MeromorphicAt f p := hg.meromorphicAt.div hline.meromorphicAt
      have ho : meromorphicOrderAt f p = (-1 : ℤ) := by
        refine (meromorphicOrderAt_eq_int_iff hm).mpr ⟨g, hg, hn, ?_⟩
        exact Filter.Eventually.of_forall fun z => by
          simp [f, div_eq_inv_mul]
      exact hp (by rw [ho]; exact_mod_cast (show (-1 : ℤ) < 0 by decide))
    show (principalPartAt f p).coeff 0 = g p
    simp [principalPartAt, hp, hz]

/-- For an analytic numerator over a pole of exact order `n + 1`,
the residue is the Taylor coefficient of degree `n`. -/
theorem meromorphicResidue_div_sub_pow {g : ℂ → ℂ} {p : ℂ} (n : ℕ)
    (hg : AnalyticAt ℂ g p) (hne : g p ≠ 0) :
    meromorphicResidue (fun z => g z / (z - p) ^ (n + 1)) p =
      iteratedDeriv n g p / (n.factorial : ℂ) := by
  let f := fun z => g z / (z - p) ^ (n + 1)
  let P := principalPartOfNumerator g p n
  have hP : P.Represents f := principalPartOfNumerator_represents hg
  have hm : MeromorphicAt f p := hg.meromorphicAt.div
    ((show AnalyticAt ℂ (fun z => z - p) p by fun_prop).pow _).meromorphicAt
  have horder : meromorphicOrderAt f p = (-((n : ℤ) + 1) : ℤ) := by
    refine (meromorphicOrderAt_eq_int_iff hm).mpr ⟨g, hg, hne, ?_⟩
    exact Eventually.of_forall fun z => by
      have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [hn, zpow_neg, zpow_natCast]
      simp [f, div_eq_inv_mul]
  have hp : meromorphicOrderAt f p < 0 := by
    rw [horder]
    exact_mod_cast (show -((n : ℤ) + 1) < 0 by omega)
  have hcoeff := PrincipalPart.residue_eq_of_eventuallyEq
    (P := principalPartAt f p) (Q := P) (principalPartAt_center f p) EventuallyEq.rfl
    (principalPartAt_represents hp) hP
  simpa [meromorphicResidue, P, principalPartOfNumerator] using hcoeff

/-- The simple-pole specialization of B.3.2.1. A holomorphic test
multiplies the residue by its value at the pole. -/
theorem meromorphicResidue_mul_of_simplePole {f Φ : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hΦ : AnalyticAt ℂ Φ p)
    (horder : meromorphicOrderAt f p = -1) :
    meromorphicResidue (Φ * f) p = Φ p * meromorphicResidue f p := by
  obtain ⟨g, hg, -, he⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) hf).mp horder
  have hDiv : f =ᶠ[nhdsWithin p {p}ᶜ] fun z => g z / (z - p) := by
    filter_upwards [he] with z hz
    simpa only [zpow_neg_one, smul_eq_mul, div_eq_inv_mul] using hz
  have hMul : (Φ * f) =ᶠ[nhdsWithin p {p}ᶜ] fun z => (Φ z * g z) / (z - p) := by
    filter_upwards [hDiv] with z hz
    change Φ z * f z = _
    rw [hz, mul_div_assoc]
  rw [meromorphicResidue_congr hMul, meromorphicResidue_div_sub (hΦ.fun_mul hg),
    meromorphicResidue_congr hDiv, meromorphicResidue_div_sub hg]

/-- Changing to normal form leaves the residue at each point unchanged. -/
theorem meromorphicResidue_toMeromorphicNFOn {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hf : MeromorphicOn f U) (hp : p ∈ U) :
    meromorphicResidue (toMeromorphicNFOn f U) p = meromorphicResidue f p :=
  meromorphicResidue_congr (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hp)

/-- One may index the residues of the product by the original poles.
If the test function cancels a pole, its term is zero. -/
theorem sum_rectanglePoles_normalized_product {f Φ : ℂ → ℂ} {U : Set ℂ} {a b c d : ℝ}
    (hR : [[a, b]] ×ℂ [[c, d]] ⊆ U)
    (hf : MeromorphicOn f U) (hΦ : AnalyticOnNhd ℂ Φ U) :
    let G := Φ * f
    let F := toMeromorphicNFOn G U
    (∑ p ∈ rectanglePoles F a b c d
      (fun z hz => (meromorphicNFOn_toMeromorphicNFOn G U).meromorphicOn z (hR hz)),
        meromorphicResidue F p) =
      ∑ p ∈ rectanglePoles f a b c d (fun z hz => hf z (hR hz)), meromorphicResidue G p := by
  dsimp only
  let G := Φ * f
  let F := toMeromorphicNFOn G U
  have hG : MeromorphicOn G U := fun z hz => (hΦ z hz).meromorphicAt.mul (hf z hz)
  let s := rectanglePoles F a b c d
    (fun z hz => (meromorphicNFOn_toMeromorphicNFOn G U).meromorphicOn z (hR hz))
  let t := rectanglePoles f a b c d (fun z hz => hf z (hR hz))
  change (∑ p ∈ s, meromorphicResidue F p) = ∑ p ∈ t, meromorphicResidue G p
  calc
    _ = ∑ p ∈ s, meromorphicResidue G p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact meromorphicResidue_toMeromorphicNFOn hG (hR (mem_rectanglePoles.mp hp).1)
    _ = _ := by
      apply Finset.sum_subset
      · intro p hp
        obtain ⟨hU, ho⟩ := mem_rectanglePoles.mp hp
        refine mem_rectanglePoles.mpr ⟨hU, ?_⟩
        rw [meromorphicOrderAt_toMeromorphicNFOn hG (hR hU),
          meromorphicOrderAt_mul (hΦ p (hR hU)).meromorphicAt (hf p (hR hU))] at ho
        exact lt_of_not_ge (fun h => (not_lt_of_ge
          (add_nonneg (hΦ p (hR hU)).meromorphicOrderAt_nonneg h)) ho)
      · intro p hp hn
        have hU := (mem_rectanglePoles.mp hp).1
        have h : ¬meromorphicOrderAt G p < 0 := fun hh => hn (mem_rectanglePoles.mpr ⟨hU, by
          rwa [meromorphicOrderAt_toMeromorphicNFOn hG (hR hU)]⟩)
        simp [meromorphicResidue, principalPartAt, h]

/-- Corrected B.3.2.1 for a meromorphic function and a holomorphic test
function. The polynomial bounds hold on the chosen vertical lines and
on the two horizontal lines in terms of their heights. The sum uses
the full residue of the product at each pole of the original function. -/
theorem asymptotic_residue_product {f Φ : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ} {m : ℕ}
    (hab : a < b) (hf : MeromorphicOn f (Complex.re ⁻¹' Icc a b))
    (hΦ : AnalyticOnNhd ℂ Φ (Complex.re ⁻¹' Icc a b))
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hHoriz : ∃ A C : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop, ∀ x ∈ Icc a b,
      ∀ y ∈ ({low j, high j} : Set ℝ),
        AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I) ∧
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ A * |y| ^ m ∧
        |y| ^ (m + 1) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ C)
    (hVert : ∀ x ∈ ({a, b} : Set ℝ),
      (∀ y : ℝ, AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I)) ∧
      ∃ B D R : ℝ, 0 ≤ B ∧ ∀ y : ℝ, R ≤ |y| →
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * |y| ^ m ∧
        |y| ^ (m + 2) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ D) :
    let W := fun x y : ℝ => Φ ((x : ℂ) + (y : ℂ) * I) * f ((x : ℂ) + (y : ℂ) * I)
    Integrable (W a) ∧ Integrable (W b) ∧
    Tendsto (fun j => ∑ p ∈ rectanglePoles f a b (low j) (high j)
      (fun z hz => hf z (rectangle_in_strip hab hz)), meromorphicResidue (Φ * f) p) atTop
      (nhds ((I * (∫ y : ℝ, W b y) - I * (∫ y : ℝ, W a y)) / (2 * Real.pi * I))) := by
  dsimp only
  let U := Complex.re ⁻¹' Icc a b
  let G := fun z => Φ z * f z
  let F := toMeromorphicNFOn G U
  have hG : MeromorphicOn G U := fun z hz =>
    (hΦ z hz).meromorphicAt.mul (hf z hz)
  have hF : MeromorphicNFOn F U := meromorphicNFOn_toMeromorphicNFOn G U
  have hline (x y : ℝ) (hx : x ∈ Icc a b) :
      ((x : ℂ) + (y : ℂ) * I) ∈ U := by simpa [U, Complex.mul_re]
  have hnorm (z : ℂ) (hz : z ∈ U) (ha : AnalyticAt ℂ f z) :
      F z = G z ∧ AnalyticAt ℂ F z := by
    have hGz : AnalyticAt ℂ G z := (hΦ z hz).fun_mul ha
    have hp : toMeromorphicNFAt G z = G := toMeromorphicNFAt_eq_self.mpr hGz.meromorphicNFAt
    have heq := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hG hz
    rw [hp] at heq
    exact ⟨heq.eq_of_nhds, hGz.congr heq.symm⟩
  have hprod (x y : ℝ) (hx : x ∈ Icc a b)
      (ha : AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I)) {A C : ℝ}
      (hA : 0 ≤ A) (n : ℕ)
      (h1 : ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ A * |y| ^ m)
      (h2 : |y| ^ (m + n) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ C) :
      |y| ^ n * ‖F ((x : ℂ) + (y : ℂ) * I)‖ ≤ A * C := by
    rw [(hnorm _ (hline x y hx) ha).1, norm_mul]
    calc
      _ ≤ |y| ^ n * (‖Φ ((x : ℂ) + (y : ℂ) * I)‖ * (A * |y| ^ m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (by positivity)
      _ = A * (|y| ^ (m + n) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hA
  have hside (x : ℝ) (hx : x ∈ ({a, b} : Set ℝ)) : x ∈ Icc a b := by
    rcases mem_insert_iff.mp hx with hh | hh
    · simpa [hh] using show a ∈ Icc a b from ⟨le_rfl, hab.le⟩
    · simpa [mem_singleton_iff.mp hh] using show b ∈ Icc a b from ⟨hab.le, le_rfl⟩
  have hV (x : ℝ) (hx : x ∈ ({a, b} : Set ℝ)) :
      (∀ y : ℝ, AnalyticAt ℂ F ((x : ℂ) + (y : ℂ) * I)) ∧
      ∃ C R : ℝ, ∀ y : ℝ, R ≤ |y| → |y| ^ 2 * ‖F ((x : ℂ) + (y : ℂ) * I)‖ ≤ C := by
    obtain ⟨ha, B, D, R, hB, hBounds⟩ := hVert x hx
    exact ⟨fun y => (hnorm _ (hline x y (hside x hx)) (ha y)).2, B * D, R,
      fun y hy => hprod x y (hside x hx) (ha y) hB 2 (hBounds y hy).1 (hBounds y hy).2⟩
  have hH : ∃ C : ℝ, ∀ᶠ j in atTop, ∀ x ∈ Icc a b,
      (AnalyticAt ℂ F ((x : ℂ) + (low j : ℂ) * I) ∧
        AnalyticAt ℂ F ((x : ℂ) + (high j : ℂ) * I)) ∧
      (|low j| * ‖F ((x : ℂ) + (low j : ℂ) * I)‖ ≤ C ∧
        |high j| * ‖F ((x : ℂ) + (high j : ℂ) * I)‖ ≤ C) := by
    obtain ⟨A, C, hA, hAC⟩ := hHoriz
    refine ⟨A * C, ?_⟩
    filter_upwards [hAC] with j hj
    intro x hx
    have hL := hj x hx (low j) (by simp)
    have hU := hj x hx (high j) (by simp)
    refine ⟨⟨(hnorm _ (hline x _ hx) hL.1).2, (hnorm _ (hline x _ hx) hU.1).2⟩, ?_, ?_⟩
    · simpa only [pow_one] using hprod x _ hx hL.1 hA 1 hL.2.1 hL.2.2
    · simpa only [pow_one] using hprod x _ hx hU.1 hA 1 hU.2.1 hU.2.2
  have he (x : ℝ) (hx : x ∈ ({a, b} : Set ℝ)) :
      (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * I)) =
        (fun y : ℝ => Φ ((x : ℂ) + (y : ℂ) * I) * f ((x : ℂ) + (y : ℂ) * I)) :=
    funext fun y => (hnorm _ (hline x y (hside x hx)) ((hVert x hx).1 y)).1
  have hh := asymptotic_residue hab hF hlo hhi hH hV
  dsimp only at hh
  rw [he a (by simp), he b (by simp)] at hh
  refine ⟨hh.1, hh.2.1, hh.2.2.congr' (Eventually.of_forall fun j => ?_)⟩
  exact sum_rectanglePoles_normalized_product
    (c := low j) (d := high j) (rectangle_in_strip hab) hf hΦ

/-- B.3.2.1 with simple poles. The product residues in the general rectangle
limit can then be written as the stated evaluation weights. -/
theorem asymptotic_residue_simplePoles {f Φ : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ} {m : ℕ}
    (hab : a < b) (hf : MeromorphicOn f (Complex.re ⁻¹' Icc a b))
    (hΦ : AnalyticOnNhd ℂ Φ (Complex.re ⁻¹' Icc a b))
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hHoriz : ∃ A C : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop, ∀ x ∈ Icc a b,
      ∀ y ∈ ({low j, high j} : Set ℝ),
        AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I) ∧
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ A * |y| ^ m ∧
        |y| ^ (m + 1) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ C)
    (hVert : ∀ x ∈ ({a, b} : Set ℝ),
      (∀ y : ℝ, AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I)) ∧
      ∃ B D R : ℝ, 0 ≤ B ∧ ∀ y : ℝ, R ≤ |y| →
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * |y| ^ m ∧
        |y| ^ (m + 2) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ D)
    (hSimple : ∀ p ∈ Complex.re ⁻¹' Icc a b,
      meromorphicOrderAt f p < 0 → meromorphicOrderAt f p = -1) :
    let W := fun x y : ℝ => Φ ((x : ℂ) + (y : ℂ) * I) * f ((x : ℂ) + (y : ℂ) * I)
    Integrable (W a) ∧ Integrable (W b) ∧
    Tendsto (fun j => ∑ p ∈ rectanglePoles f a b (low j) (high j)
      (fun z hz => hf z (rectangle_in_strip hab hz)), Φ p * meromorphicResidue f p) atTop
      (nhds ((I * (∫ y : ℝ, W b y) - I * (∫ y : ℝ, W a y)) / (2 * Real.pi * I))) := by
  obtain ⟨ha, hb, hLimit⟩ := asymptotic_residue_product hab hf hΦ hlo hhi hHoriz hVert
  refine ⟨ha, hb, hLimit.congr fun j => Finset.sum_congr rfl fun p hp => ?_⟩
  obtain ⟨hRect, hPole⟩ := mem_rectanglePoles.mp hp
  have hStrip := rectangle_in_strip hab hRect
  exact meromorphicResidue_mul_of_simplePole (hf p hStrip) (hΦ p hStrip)
    (hSimple p hStrip hPole)

end Masullo
