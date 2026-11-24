import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Function MeasureTheory Set Topology

namespace Masullo

/-- The fundamental theorem of calculus with finitely many one-sided
jumps. The values of the function at the jumps are immaterial. -/
theorem integral_derivative_add_jumps
    {u v : ℝ → ℂ} {left right : ℝ → ℂ} (S : Finset ℝ) {a b : ℝ} {A B : ℂ}
    (hab : a < b) (hv : Integrable v)
    (hderiv : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt u (v x) x)
    (ha : Tendsto u (𝓝[>] a) (𝓝 A)) (hb : Tendsto u (𝓝[<] b) (𝓝 B))
    (hleft : ∀ x ∈ S, x ∈ Ioo a b → Tendsto u (𝓝[<] x) (𝓝 (left x)))
    (hright : ∀ x ∈ S, x ∈ Ioo a b → Tendsto u (𝓝[>] x) (𝓝 (right x))) :
    (∫ x in a..b, v x) + ∑ c ∈ S, (if c ∈ Ioo a b then right c - left c else 0) =
      B - A := by
  classical
  induction S using Finset.induction_on generalizing a b A B with
  | empty =>
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab
      (fun x hx => hderiv x hx (Finset.notMem_empty x)) hv.intervalIntegrable ha hb
  | insert c S hc ih =>
    rw [Finset.sum_insert hc]
    by_cases hcab : c ∈ Ioo a b
    · obtain ⟨hac, hcb⟩ := hcab
      have hcab : c ∈ Ioo a b := ⟨hac, hcb⟩
      have hLI (x : ℝ) (hx : x ∈ Ioo a c) : x ∈ Ioo a b := ⟨hx.1, hx.2.trans hcb⟩
      have hRI (x : ℝ) (hx : x ∈ Ioo c b) : x ∈ Ioo a b := ⟨hac.trans hx.1, hx.2⟩
      have hL := ih hac (fun x hx hxS =>
          hderiv x (hLI x hx) (fun hh => (Finset.mem_insert.mp hh).elim hx.2.ne hxS))
        ha (hleft c (Finset.mem_insert_self _ _) hcab)
        (fun x hx hxi => hleft x (Finset.mem_insert_of_mem hx) (hLI x hxi))
        (fun x hx hxi => hright x (Finset.mem_insert_of_mem hx) (hLI x hxi))
      have hR := ih hcb (fun x hx hxS =>
          hderiv x (hRI x hx) (fun hh => (Finset.mem_insert.mp hh).elim hx.1.ne' hxS))
        (hright c (Finset.mem_insert_self _ _) hcab) hb
        (fun x hx hxi => hleft x (Finset.mem_insert_of_mem hx) (hRI x hxi))
        (fun x hx hxi => hright x (Finset.mem_insert_of_mem hx) (hRI x hxi))
      have hsum : (∑ x ∈ S, (if x ∈ Ioo a b then right x - left x else 0)) =
          (∑ x ∈ S, (if x ∈ Ioo a c then right x - left x else 0)) +
          (∑ x ∈ S, (if x ∈ Ioo c b then right x - left x else 0)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        rcases lt_trichotomy x c with h | h | h
        · have he : x ∈ Ioo a b ↔ x ∈ Ioo a c :=
            ⟨fun hh => ⟨hh.1, h⟩, hLI x⟩
          simp [he, show x ∉ Ioo c b from fun hh => h.asymm hh.1]
        · subst x
          exact (hc hx).elim
        · have he : x ∈ Ioo a b ↔ x ∈ Ioo c b :=
            ⟨fun hh => ⟨h, hh.2⟩, hRI x⟩
          simp [he, show x ∉ Ioo a c from fun hh => h.asymm hh.2]
      rw [ite_eq_left hcab, hsum, ← intervalIntegral.integral_add_adjacent_intervals
        hv.intervalIntegrable hv.intervalIntegrable]
      linear_combination hL + hR
    · rw [ite_eq_right hcab, zero_add]
      exact ih hab (fun x hx hn =>
        hderiv x hx (fun hh => (Finset.mem_insert.mp hh).elim (fun he => hcab (he ▸ hx)) hn)) ha hb
        (fun x hx => hleft x (Finset.mem_insert_of_mem hx))
        (fun x hx => hright x (Finset.mem_insert_of_mem hx))

end Masullo
