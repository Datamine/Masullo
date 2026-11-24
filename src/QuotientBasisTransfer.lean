import AbsoluteBasisDuality
import QuotientDuals
import FrechetFactorization
import Mathlib.Topology.Algebra.InfiniteSum.Module

open Bornology Filter Function Set Topology TopologicalSpace
open scoped Uniformity NNReal

namespace Masullo

noncomputable section

section Transfer

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- A linear homeomorphism pulls the basis and its absolute seminorm bounds back together. -/
theorem absoluteBasis_pullback (e : X ≃L[ℂ] Y) {x : ℕ → X} {y : ℕ → Y}
    (hxy : ∀ n, e (x n) = y n) {f : ℕ → StrongDual ℂ Y}
    (hb : IsSchauderBasis y f) (ha : IsAbsolute y f) :
    IsSchauderBasis x (fun n => (f n).comp e.toContinuousLinearMap) ∧
      IsAbsolute x (fun n => (f n).comp e.toContinuousLinearMap) := by
  have hx (n : ℕ) : e.symm (y n) = x n := by rw [← hxy n, e.symm_apply_apply]
  constructor
  · refine ⟨fun m n => ?_, fun u => ?_⟩
    · change f m (e (x n)) = _
      rw [hxy]
      exact hb.1 m n
    · have h := e.symm.toContinuousLinearMap.hasSum (hb.2 (e u))
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.comp_apply, map_smul, hx, e.symm_apply_apply] using h
  · intro q hq
    let p := q.comp e.symm.toLinearMap
    obtain ⟨r, hr, habs⟩ := ha p (hq.comp e.symm.continuous)
    refine ⟨r.comp e.toLinearMap, hr.comp e.continuous, fun u => ?_⟩
    have he (n : ℕ) : p (f n (e u) • y n) = q (f n (e u) • x n) := by
      change q (e.symm (f n (e u) • y n)) = _
      rw [map_smul, hx]
    change Summable (fun n => q (f n (e u) • x n)) ∧
      (∑' n, q (f n (e u) • x n)) ≤ r (e u)
    simpa only [he] using habs (e u)

end Transfer

section Dual

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
  {x : ℕ → X} {f : ℕ → StrongDual ℂ X}

/-- Compact closure of bounded sets upgrades the scalar basis expansions
to unconditional convergence in the strong dual. -/
theorem absoluteBasis_strongDual_of_compactClosure
    (hcompact : ∀ B : Set X, IsVonNBounded ℂ B → IsCompact (closure B))
    (hb : IsSchauderBasis x f) (ha : IsAbsolute x f) :
    IsShrinking x f ∧ IsUnconditional f (fun n => strongBidualEvaluation (x n)) := by
  classical
  have hsum (g : StrongDual ℂ X) :
      HasSum (fun n => g (x n) • f n) g := by
    let q : Seminorm ℂ X := (normSeminorm ℂ ℂ).comp g.toLinearMap
    have hq : Continuous q := g.continuous.norm
    obtain ⟨r, hr, hsum⟩ := ha q hq
    let Q (s : Finset ℕ) : StrongDual ℂ X := ∑ n ∈ s, g (x n) • f n
    have hQ (s : Finset ℕ) (u : X) : Q s u = ∑ n ∈ s, f n u • g (x n) := by
      simp only [Q, sum_apply, smul_apply, smul_eq_mul,
        mul_comm]
    have herror (s : Finset ℕ) (u : X) : ‖(Q s - g) u‖ ≤ r u + q u := by
      have hnorm : ‖Q s u‖ ≤ r u := by
        rw [hQ]
        calc
          _ ≤ ∑ n ∈ s, ‖f n u • g (x n)‖ := norm_sum_le _ _
          _ = ∑ n ∈ s, q (f n u • x n) := by simp [q, map_smul]
          _ ≤ ∑' n, q (f n u • x n) :=
            (hsum u).1.sum_le_tsum s (fun _ _ => apply_nonneg _ _)
          _ ≤ _ := (hsum u).2
      exact (norm_sub_le (Q s u) (g u)).trans (add_le_add_left hnorm _)
    have hpoint (u : X) : Tendsto (fun s : Finset ℕ => Q s u) atTop (𝓝 (g u)) := by
      have hn : Summable (fun n => ‖f n u • g (x n)‖) := by
        simpa [q, map_smul] using (hsum u).1
      have h := hn.of_norm
      have ho := g.hasSum (hb.2 u)
      have hs : HasSum (fun n => f n u • g (x n)) (g u) (SummationFilter.conditional ℕ) := by
        simpa only [map_smul] using ho
      have he := hs.unique (Tendsto.mono_left h.hasSum (SummationFilter.conditional ℕ).le_atTop)
      have hh := h.hasSum
      change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, f n u • g (x n)) atTop
        (𝓝 (∑' n, f n u • g (x n))) at hh
      simpa only [hQ, ← he] using hh
    change Tendsto Q atTop (𝓝 g)
    apply tendsto_sub_nhds_zero_iff.mp
    apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_ball).tendsto_right_iff.mpr
    rintro ⟨B, ε⟩ ⟨hB, hε⟩
    let U (v : X) := {u : X | r (u - v) + q (u - v) < ε / 2}
    have hU (v : X) : IsOpen (U v) :=
      isOpen_lt ((hr.comp (continuous_id.sub continuous_const)).add
        (hq.comp (continuous_id.sub continuous_const))) continuous_const
    have hcv : closure B ⊆ ⋃ v, U v := fun u _ => mem_iUnion.mpr ⟨u, by
      change r (u - u) + q (u - u) < _
      simpa using half_pos hε⟩
    obtain ⟨T, hT⟩ := (hcompact B hB).elim_finite_subcover U hU hcv
    have hnear : ∀ᶠ s : Finset ℕ in atTop, ∀ v ∈ T, ‖(Q s - g) v‖ < ε / 2 :=
      (Finset.eventually_all T).mpr fun v _ => by
        simpa only [sub_apply, dist_eq_norm] using
          (Metric.tendsto_nhds.mp (hpoint v)) _ (half_pos hε)
    filter_upwards [hnear] with s hs u hu
    obtain ⟨v, hv, huv⟩ := mem_iUnion₂.mp (hT (subset_closure hu))
    have hsplit : (Q s - g) u = (Q s - g) (u - v) + (Q s - g) v := by
      rw [← map_add, sub_add_cancel]
    rw [Metric.mem_ball, dist_zero_right]
    rw [hsplit]
    exact (norm_add_le _ _).trans_lt
      (by linarith [herror s (u - v), hs v hv, show r (u - v) + q (u - v) < ε / 2 from huv])
  have hu : IsUnconditional f (fun n => strongBidualEvaluation (x n)) := hsum
  refine ⟨⟨fun m n => ?_, fun g => ?_⟩, hu⟩
  · change f n (x m) = _
    by_cases h : m = n
    · simp [hb.1, h]
    · simp [hb.1, h, Ne.symm h]
  · exact Tendsto.mono_left (hsum g) (SummationFilter.conditional ℕ).le_atTop

end Dual

section Quotients

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]

/-- Lemma 7.3.1.5. Transport the absolute basis, its strong-dual basis and all
seminorm bounds along the isomorphism induced by the original linear map.
It is sufficient for each chosen lift to agree after the second quotient. -/
theorem quotient_absoluteBasis_transfer
    (H₁ : Submodule ℂ E₁) (H₂ : Submodule ℂ E₂)
    (hH₁ : IsClosed (H₁ : Set E₁)) (hH₂ : IsClosed (H₂ : Set E₂))
    (hN₁ : NuclearLocallyConvex.{u, u} E₁) (hN₂ : NuclearLocallyConvex.{v, v} E₂)
    (hFr₁ : IsFrechetTVS E₁) (hFr₂ : IsFrechetTVS E₂)
    (A : E₁ →L[ℂ] E₂) (_hA : Injective A)
    (hker : ∀ a, A a ∈ H₂ ↔ a ∈ H₁)
    (hsurj : Surjective (H₂.mkQL.comp A))
    (x : ℕ → E₂) (f : ℕ → StrongDual ℂ (E₂ ⧸ H₂))
    (hb : IsSchauderBasis (H₂.mkQ ∘ x) f) (ha : IsAbsolute (H₂.mkQ ∘ x) f)
    (F : Seminorm ℂ (E₂ ⧸ H₂) → ℕ → ℝ≥0)
    (hF : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, q (H₂.mkQ (x n)) ≤ C * (F q n : ℝ)) :
    letI : PolynormableSpace ℂ E₁ := hN₁.2.1
    letI : IsTopologicalAddGroup E₁ := (PolynormableSpace.withSeminorms ℂ E₁).topologicalAddGroup
    letI : ContinuousSMul ℂ E₁ := (PolynormableSpace.withSeminorms ℂ E₁).continuousSMul
    ∃ e : (E₁ ⧸ H₁) ≃L[ℂ] (E₂ ⧸ H₂),
      (∀ a, e (H₁.mkQ a) = H₂.mkQ (A a)) ∧
      ∀ (y : ℕ → E₁), (∀ n, H₂.mkQ (A (y n)) = H₂.mkQ (x n)) →
        let yq := H₁.mkQ ∘ y
        let g := fun n => (f n).comp e.toContinuousLinearMap
        IsSchauderBasis yq g ∧ IsAbsolute yq g ∧
        IsShrinking yq g ∧ IsUnconditional g (fun n => strongBidualEvaluation (yq n)) ∧
        ∀ q : Seminorm ℂ (E₁ ⧸ H₁), Continuous q →
          ∃ C : ℝ, 0 < C ∧
            ∀ᶠ n in atTop, q (yq n) ≤ C * (F (q.comp e.symm.toLinearMap) n : ℝ) := by
  classical
  have hcompact (B : Set (E₁ ⧸ H₁)) (hB : IsVonNBounded ℂ B) : IsCompact (closure B) := by
    obtain ⟨K, hK, he⟩ := nuclearFrechet_quotient_compactLift H₁ hH₁ hN₁ hFr₁ hB
    rw [← he]
    exact hK.image H₁.mkQL.continuous
  obtain ⟨hadd₁, hpoly₁, hmetr₁, hcomplete₁⟩ := hFr₁
  obtain ⟨hadd₂, hpoly₂, hmetr₂, hcomplete₂⟩ := hFr₂
  letI : ContinuousSMul ℂ E₁ := (PolynormableSpace.withSeminorms ℂ E₁).continuousSMul
  letI : PolynormableSpace ℂ E₂ := hN₂.2.1
  letI : ContinuousSMul ℂ E₂ := (PolynormableSpace.withSeminorms ℂ E₂).continuousSMul
  letI : IsClosed (H₂ : Set E₂) := hH₂
  letI : UniformSpace E₂ := IsTopologicalAddGroup.rightUniformSpace E₂
  letI : CompleteSpace E₂ := hcomplete₂
  let Q := E₂ ⧸ H₂
  letI : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  letI : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Q := QuotientAddGroup.completeSpace_right' E₂ H₂.toAddSubgroup
  letI : (𝓝 (0 : Q)).IsCountablyGenerated := by
    rw [← H₂.mkQL.map_zero, ← H₂.isOpenQuotientMap_mkQL.map_nhds_eq]
    infer_instance
  letI : (uniformity Q).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero Q]
    infer_instance
  letI : BaireSpace Q := BaireSpace.of_completelyPseudoMetrizable
  let P := H₂.mkQL.comp A
  have hP : IsOpenMap P := isOpenMap_of_surjective_complete_baire P hsurj
  have hle : H₁ ≤ P.ker := by
    intro a ha
    change H₂.mkQ (A a) = 0
    exact (Submodule.Quotient.mk_eq_zero H₂).mpr ((hker a).mpr ha)
  let A₀ := H₁.liftQL P hle
  have hcomp : A₀ ∘ H₁.mkQ = P := rfl
  have hinj : Injective A₀ := by
    apply (injective_iff_map_eq_zero A₀).mpr
    intro z hz
    obtain ⟨a, rfl⟩ := H₁.mkQ_surjective z
    apply (Submodule.Quotient.mk_eq_zero H₁).mpr
    apply (hker a).mp
    exact (Submodule.Quotient.mk_eq_zero H₂).mp hz
  have hsurj₀ : Surjective A₀ := by
    intro z
    obtain ⟨a, ha⟩ := hsurj z
    exact ⟨H₁.mkQ a, ha⟩
  have hopen : IsOpenMap A₀ :=
    IsOpenMap.of_comp H₁.mkQL.continuous H₁.mkQ_surjective (hcomp.symm ▸ hP)
  let e₀ := LinearEquiv.ofBijective A₀.toLinearMap ⟨hinj, hsurj₀⟩
  let e : (E₁ ⧸ H₁) ≃L[ℂ] Q :=
    ⟨e₀, A₀.continuous, e₀.toEquiv.continuous_symm_iff.mpr hopen⟩
  refine ⟨e, fun _ => rfl, fun y hy => ?_⟩
  have hxy (n : ℕ) : e (H₁.mkQ (y n)) = H₂.mkQ (x n) := hy n
  obtain ⟨hb', ha'⟩ := absoluteBasis_pullback e hxy hb ha
  obtain ⟨hdual, huncond⟩ := absoluteBasis_strongDual_of_compactClosure hcompact hb' ha'
  refine ⟨hb', ha', hdual, huncond, fun q hq => ?_⟩
  obtain ⟨C, hC, hmajor⟩ := hF (q.comp e.symm.toLinearMap) (hq.comp e.symm.continuous)
  refine ⟨C, hC, hmajor.mono fun n hn => ?_⟩
  change q (e.symm (H₂.mkQ (x n))) ≤ _ at hn
  rwa [← hxy n, e.symm_apply_apply] at hn

end Quotients

end

end Masullo
