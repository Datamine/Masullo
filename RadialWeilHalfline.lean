import RadialWeilFrequencyDivision

open Set Function
open scoped SchwartzMap

namespace Masullo
noncomputable section

private abbrev S := 𝓢(ℝ, ℂ)

private theorem compactSupport_shift (f : S) (hf : HasCompactSupport f) (d : ℝ) :
    HasCompactSupport (f.compSubConstCLM ℂ d) := by
  change HasCompactSupport (fun x : ℝ ↦ f (x - d))
  have h := hf.comp_homeomorph (Homeomorph.addRight (-d))
  change HasCompactSupport (fun x : ℝ ↦ f (x + -d)) at h
  simpa only [sub_eq_add_neg] using h

set_option maxHeartbeats 600000 in
private theorem exists_leftShift_solve (b : ℝ) (hb : 0 < b) (c : ℂ) (a : ℝ)
    (f : S) (hf : HasCompactSupport f) :
    ∃ g : S, HasCompactSupport g ∧ ∀ x ≥ a, g x - c * g (x+b) = f x := by
  let g : ℕ → S := Nat.rec (0 : S) (fun _ u ↦ f + c • u.compSubConstCLM ℂ (-b))
  have hcomp (n : ℕ) : HasCompactSupport (g n) := by
    induction n with
    | zero =>
      change HasCompactSupport (0 : ℝ → ℂ)
      exact HasCompactSupport.zero
    | succ n ih =>
      change HasCompactSupport ((f : ℝ → ℂ) + c • ((g n).compSubConstCLM ℂ (-b) : ℝ → ℂ))
      exact hf.add ((compactSupport_shift (g n) ih (-b)).smul_left)
  have he (n : ℕ) (x : ℝ) : g n x - c * g n (x+b) = f x - c^n * f (x+(n : ℝ)*b) := by
    induction n generalizing x with
    | zero => simp [g]
    | succ n ih =>
      change ((f + c • (g n).compSubConstCLM ℂ (-b)) : S) x -
        c * ((f + c • (g n).compSubConstCLM ℂ (-b)) : S) (x+b) = _
      simp only [add_apply, _root_.smul_apply, SchwartzMap.compSubConstCLM_apply,
        sub_neg_eq_add, smul_eq_mul]
      have h : x + b + (n : ℝ)*b = x + (↑(n+1) : ℝ)*b := by push_cast; ring
      have hn := ih (x+b)
      rw [h] at hn
      rw [pow_succ]
      linear_combination c * hn
  obtain ⟨M, hM⟩ := hf.isCompact.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt ((M-a)/b)
  refine ⟨g n,hcomp n,fun x hx ↦ ?_⟩
  have hgt : M < x+(n : ℝ)*b := by
    have h := (div_lt_iff₀ hb).mp hn
    linarith
  have hz : f (x+(n : ℝ)*b) = 0 :=
    notMem_support.mp (fun h ↦ hgt.not_ge (hM (subset_tsupport f h)))
  rw [he, hz, mul_zero, sub_zero]

private theorem exists_radialWeilDifference_solve_halfline (d : ℝ) (hd : d ≠ 0) (c : ℂ)
    (a : ℝ) (f : S) (hf : HasCompactSupport f) :
    ∃ g : S, HasCompactSupport g ∧ ∀ x ≥ a, g x - c * g (x-d) = f x := by
  by_cases hc : c = 0
  · exact ⟨f,hf,fun x _ ↦ by simp [hc]⟩
  rcases lt_or_gt_of_ne hd with hd' | hd'
  · obtain ⟨g,hg,h⟩ := exists_leftShift_solve (-d) (neg_pos.mpr hd') c a f hf
    exact ⟨g,hg,fun x hx ↦ by simpa only [sub_eq_add_neg] using h x hx⟩
  · let f₁ := (-c⁻¹) • f.compSubConstCLM ℂ (-d)
    have hf₁ : HasCompactSupport f₁ := (compactSupport_shift f hf (-d)).smul_left
    obtain ⟨g,hg,h⟩ := exists_leftShift_solve d hd' c⁻¹ (a-d) f₁ hf₁
    refine ⟨g,hg,fun x hx ↦ ?_⟩
    have he := h (x-d) (sub_le_sub_right hx d)
    simp only [f₁, _root_.smul_apply, SchwartzMap.compSubConstCLM_apply,
      sub_neg_eq_add, sub_add_cancel, smul_eq_mul] at he
    have hh := congrArg (fun y : ℂ ↦ -c*y) he
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    linear_combination hh + (f x - g x) * hcc

/-- Every compact Schwartz profile can be realized on a right half-line as a
finite product of phased translation differences of a compact Schwartz profile. -/
theorem radialWeilDifferenceProduct_surjOn_halfline (ds : List (ℝ × ℂ))
    (hd : ∀ p ∈ ds, p.1 ≠ 0) (a : ℝ) (f : S) (hf : HasCompactSupport f) :
    ∃ g : S, HasCompactSupport g ∧ Set.EqOn (radialWeilDifferenceProduct ds g) f (Ici a) := by
  induction ds generalizing a f with
  | nil => exact ⟨f,hf,fun _ _ ↦ rfl⟩
  | cons p ds ih =>
    obtain ⟨w,hw,h⟩ := exists_radialWeilDifference_solve_halfline p.1
      (hd p List.mem_cons_self) p.2 a f hf
    obtain ⟨g,hg,hgEq⟩ := ih (fun q hq ↦ hd q (List.mem_cons_of_mem _ hq))
      (min a (a-p.1)) w hw
    refine ⟨g,hg,fun x hx ↦ ?_⟩
    change radialWeilDifferenceProduct ds g x - p.2 * radialWeilDifferenceProduct ds g (x-p.1) = f x
    have hx₁ : x ∈ Ici (min a (a-p.1)) := by
      change min a (a-p.1) ≤ x
      exact (min_le_left _ _).trans hx
    have hx₂ : x-p.1 ∈ Ici (min a (a-p.1)) := by
      change min a (a-p.1) ≤ x-p.1
      exact (min_le_right _ _).trans (sub_le_sub_right hx _)
    rw [hgEq hx₁, hgEq hx₂]
    exact h x hx

end
end Masullo
