import RadialWeilFrequencyDivision
import MellinTaylorContinuation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo
noncomputable section

private abbrev S := 𝓢(ℝ, ℂ)

/-- The distinct real frequencies, each carrying its actual multiplicity. -/
def radialWeilJetIndices (ds : List (ℝ × ℂ)) : Set (ℝ × ℕ) :=
  {p | p.2 < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 p.1 = 0))}

theorem radialWeilJetIndices_countable (ds : List (ℝ × ℂ)) (hd : ∀ p ∈ ds, p.1 ≠ 0) :
    (radialWeilJetIndices ds).Countable := by
  let X (n : ℕ) := {p : ℝ × ℕ | p.1 ∈ Icc (-(n : ℝ)) (n : ℝ) ∧ p ∈ radialWeilJetIndices ds}
  have hf (n : ℕ) : (X n).Finite := radialWeilProduct_finite_moment_indices ds hd _ isCompact_Icc
  apply (Set.countable_iUnion (fun n ↦ (hf n).countable)).mono
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt |x.1|
  exact mem_iUnion.mpr ⟨n, ⟨abs_le.mp hn.le, hx⟩⟩

private theorem radialWeilJet_exists_isolating_ball (ds : List (ℝ × ℂ)) (hd : ∀ p ∈ ds, p.1 ≠ 0)
    (a : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ radialWeilJetIndices ds, p.1 ∈ Metric.ball a ε → p.1 = a := by
  let X := {p : ℝ × ℕ | p.1 ∈ Icc (a-1) (a+1) ∧ p ∈ radialWeilJetIndices ds}
  have hX : X.Finite := radialWeilProduct_finite_moment_indices ds hd _ isCompact_Icc
  let Z := Prod.fst '' X \ {a}
  have hZ : Z.Finite := (hX.image Prod.fst).sdiff
  let U := Ioo (a-1) (a+1) ∩ Zᶜ
  have hU : U ∈ 𝓝 a := by
    apply (isOpen_Ioo.inter hZ.isClosed.isOpen_compl).mem_nhds
    exact ⟨⟨by linarith, by linarith⟩, fun hz ↦ hz.2 rfl⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε, hε, fun p hp hpε ↦ ?_⟩
  have h := hsub hpε
  by_contra hn
  exact h.2 ⟨⟨p, ⟨⟨h.1.1.le, h.1.2.le⟩, hp⟩, rfl⟩, hn⟩

private theorem translated_monomial_jet (a : ℝ) (m j : ℕ) :
    iteratedDeriv j (fun x : ℝ ↦ (((x-a)^m : ℝ) : ℂ)) a =
      if j = m then (m.factorial : ℂ) else 0 := by
  have h : ContDiff ℝ ∞ (fun x : ℝ ↦ (x-a)^m) := (contDiff_id.sub contDiff_const).pow m
  rw [iteratedDeriv_complex_ofReal j h]
  rw [iteratedDeriv_comp_sub_const (f := fun x : ℝ ↦ x^m)]
  simp only [sub_self]
  rw [iteratedDeriv_fun_pow_zero]
  by_cases hj : j = m <;> simp [hj]

/-- A compactly supported frequency profile picks out a single jet of the
radial Weil multiplier, including when several derivatives share a center. -/
theorem exists_radialWeilJet_frequency_interpolant (ds : List (ℝ × ℂ))
    (hd : ∀ p ∈ ds, p.1 ≠ 0) (i : radialWeilJetIndices ds) :
    ∃ b : S, HasCompactSupport b ∧
      ∀ j : radialWeilJetIndices ds, iteratedDeriv j.val.2 (b : ℝ → ℂ) j.val.1 =
        if j = i then 1 else 0 := by
  classical
  let a := i.val.1
  let m := i.val.2
  obtain ⟨ε,hε,hiso⟩ := radialWeilJet_exists_isolating_ball ds hd a
  let c : ContDiffBump a := ⟨ε/4, ε/2, by positivity, by linarith⟩
  let M (x : ℝ) : ℂ := (((x-a)^m : ℝ) : ℂ)
  let d : ℂ := (m.factorial : ℂ)⁻¹
  let P (x : ℝ) := d * M x
  let v (x : ℝ) := (c x : ℂ) * P x
  have hP : ContDiff ℝ ∞ P :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ((contDiff_id.sub contDiff_const).pow m))
  have hs : ContDiff ℝ ∞ v := (Complex.ofRealCLM.contDiff.comp c.contDiff).mul hP
  have hSupp : tsupport v ⊆ Metric.closedBall a (ε/2) := by
    rw [← c.tsupport_eq]
    apply closure_mono
    intro x hx
    by_contra hn
    exact (mem_support.mp hx) (by simp [v, notMem_support.mp hn])
  have hvc : HasCompactSupport v := (isCompact_closedBall a (ε/2)).of_isClosed_subset isClosed_closure hSupp
  let b := hvc.toSchwartzMap hs
  refine ⟨b, hvc, fun j ↦ ?_⟩
  change iteratedDeriv j.val.2 v j.val.1 = _
  by_cases he : j.val.1 = a
  · have hEq : v =ᶠ[𝓝 a] P := by
      filter_upwards [c.eventuallyEq_one_of_mem_ball (Metric.mem_ball_self (by positivity : 0 < ε/4))]
        with x hx
      change c x = 1 at hx
      simp [v,hx]
    rw [he, hEq.iteratedDeriv_eq j.val.2]
    have h := translated_monomial_jet a m j.val.2
    change iteratedDeriv j.val.2 M a = _ at h
    rw [show P = d • M from rfl, iteratedDeriv_const_smul_field, smul_eq_mul, h]
    by_cases hj : j.val.2 = m
    · have hji : j = i := Subtype.ext (Prod.ext he hj)
      rw [ite_eq_left hj, ite_eq_left hji]
      exact inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m)
    · have hji : j ≠ i := fun h ↦ hj (congrArg (fun j : radialWeilJetIndices ds ↦ j.val.2) h)
      rw [ite_eq_right hj, ite_eq_right hji, mul_zero]
  · have hout : j.val.1 ∉ tsupport v := by
      intro hj
      apply he
      apply hiso j.val j.property
      exact Metric.closedBall_subset_ball (by linarith : ε/2 < ε) (hSupp hj)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hout
    have hji : j ≠ i := fun h ↦ he (congrArg (fun j : radialWeilJetIndices ds ↦ j.val.1) h)
    rw [hz.iteratedDeriv_eq, ite_eq_right hji]
    simp

end
end Masullo
