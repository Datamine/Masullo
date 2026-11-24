import InductiveLimitDuals
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Lp.lpSpace

open Bornology Filter Function Set Topology
open scoped ENNReal Pointwise

namespace Masullo.LinearInductivePresentation

noncomputable section

universe u v

variable {E : Type u} {F : ℕ → Type v}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)] [∀ n, TopologicalSpace (F n)]
variable (D : LinearInductivePresentation E F)

theorem transition_id (n : ℕ) (x : F n) : D.transition (le_refl n) x = x :=
  D.injective_incl n (D.incl_transition _ _)

theorem transition_comp {j k n : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) (x : F j) :
    D.transition hkn (D.transition hjk x) = D.transition (hjk.trans hkn) x := by
  apply D.injective_incl n
  rw [D.incl_transition, D.incl_transition, D.incl_transition]

theorem range_incl_mono {m n : ℕ} (h : m ≤ n) : range (D.incl m) ⊆ range (D.incl n) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨D.transition h x, D.incl_transition h x⟩

variable [∀ n, PolynormableSpace ℂ (F n)]

private theorem extend_step (n : ℕ) (hemb : IsEmbedding (D.transition (Nat.le_succ n)))
    (f : StrongDual ℂ (F n)) :
    ∃ g : StrongDual ℂ (F (n + 1)), ∀ x, g (D.transition (Nat.le_succ n) x) = f x := by
  let t := D.transition (Nat.le_succ n)
  let e := LinearEquiv.ofInjective t.toLinearMap hemb.injective
  have hleft : Continuous e.symm := by
    apply hemb.isInducing.continuous_iff.mpr
    change Continuous fun x => t (e.symm x)
    convert continuous_subtype_val using 1
    funext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  let g₀ : StrongDual ℂ t.toLinearMap.range := f.comp ⟨e.symm.toLinearMap, hleft⟩
  obtain ⟨g, hg⟩ := StrongDual.exists_extension t.toLinearMap.range g₀
  refine ⟨g, fun x => ?_⟩
  calc
    g (t x) = g₀ (e x) := hg (e x)
    _ = f x := congrArg f (e.symm_apply_apply x)

/-- A stage functional extends continuously to a strict countable limit. -/
private theorem extend_from_stage
    (hemb : ∀ n, IsEmbedding (D.transition (Nat.le_succ n))) (k : ℕ)
    (f : StrongDual ℂ (F k)) :
    ∃ g : StrongDual ℂ E, ∀ x, g (D.incl k x) = f x := by
  classical
  let extend (n : ℕ) (g : StrongDual ℂ (F n)) :=
    (D.extend_step n (hemb n) g).choose
  have hext (n : ℕ) (g : StrongDual ℂ (F n)) :
      ∀ x, extend n g (D.transition (Nat.le_succ n) x) = g x :=
    (D.extend_step n (hemb n) g).choose_spec
  let below (n : ℕ) (hn : n ≤ k) := f.comp (D.transition hn)
  let form : ∀ n, StrongDual ℂ (F n) := Nat.rec (below 0 (Nat.zero_le _))
    (fun n g => if h : n + 1 ≤ k then below (n + 1) h else extend n g)
  have hbelow (n : ℕ) (h : n ≤ k) : form n = below n h := by
    cases n with
    | zero => rfl
    | succ n =>
      change (if h : n + 1 ≤ k then below (n + 1) h else extend n (form n)) = _
      rw [dite_eq_left h]
  have hstep (n : ℕ) (x : F n) :
      form (n + 1) (D.transition (Nat.le_succ n) x) = form n x := by
    by_cases h : n + 1 ≤ k
    · rw [hbelow _ h, hbelow _ ((Nat.le_succ n).trans h)]
      change f (D.transition h (D.transition (Nat.le_succ n) x)) =
        f (D.transition ((Nat.le_succ n).trans h) x)
      rw [D.transition_comp]
    · simpa only [form, dite_eq_right h] using hext n (form n) x
  have hcompat (m n : ℕ) (h : m ≤ n) (x : F m) :
      form n (D.transition h x) = form m x := by
    induction n, h using Nat.le_induction with
    | base => rw [D.transition_id]
    | succ n h ih =>
      rw [← D.transition_comp h (Nat.le_succ n), hstep, ih]
  let compatible : D.CompatibleDual := ⟨form, hcompat⟩
  refine ⟨D.dualRestriction.symm compatible, fun x => ?_⟩
  have he := congrArg (fun g : D.CompatibleDual => g.val k x)
    (D.dualRestriction.apply_symm_apply compatible)
  change D.dualRestriction.symm compatible (D.incl k x) = form k x at he
  rw [he, hbelow k le_rfl]
  exact congrArg f (D.transition_id k x)

omit [∀ n, PolynormableSpace ℂ (F n)] in
private theorem all_transitions_closed (hclosed : ∀ n,
    IsClosedEmbedding (D.transition (Nat.le_succ n))) {m n : ℕ} (h : m ≤ n) :
    IsClosedEmbedding (D.transition h) := by
  induction n, h using Nat.le_induction with
  | base =>
    have he : (D.transition (le_refl m) : F m → F m) = id :=
      funext (D.transition_id m)
    rw [he]
    exact IsClosedEmbedding.id
  | succ n h ih =>
    have he : (D.transition (h.trans (Nat.le_succ n)) : F m → F (n + 1)) =
        D.transition (Nat.le_succ n) ∘ D.transition h :=
      funext fun x => (D.transition_comp h (Nat.le_succ n) x).symm
    rw [he]
    exact (hclosed n).comp ih

variable [∀ n, IsTopologicalAddGroup (F n)] [∀ n, ContinuousSMul ℂ (F n)]

private theorem separate_submodule {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [PolynormableSpace ℂ X] (S : Submodule ℂ X) (hS : IsClosed (S : Set X))
    {z : X} (hz : z ∉ S) :
    ∃ f : StrongDual ℂ X, (∀ a ∈ S, f a = 0) ∧ f z = 1 := by
  letI : Module ℝ X := Module.restrictScalars ℝ ℂ X
  letI : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  letI : LocallyConvexSpace ℝ X := (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  obtain ⟨w, β, hβ, hw⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) (S.restrictScalars ℝ).convex hS hz
  have hzero (a : X) (ha : a ∈ S) : w a = 0 := by
    by_contra h
    let c : ℂ := ((β - 1 : ℝ) : ℂ) / w a
    have hval : w (c • a) = ((β - 1 : ℝ) : ℂ) := by
      rw [map_smul]
      exact div_mul_cancel₀ _ h
    have hbound := hw (c • a) (S.smul_mem c ha)
    rw [hval] at hbound
    change β < (((β - 1 : ℝ) : ℂ)).re at hbound
    simp only [Complex.ofReal_re] at hbound
    linarith
  have hnz : w z ≠ 0 := by
    intro he
    have h := hw 0 S.zero_mem
    rw [he] at hβ
    rw [map_zero] at h
    exact (lt_asymm hβ) h
  refine ⟨(w z)⁻¹ • w, fun a ha => ?_, ?_⟩
  · change (w z)⁻¹ * w a = 0
    rw [hzero a ha, mul_zero]
  · exact inv_mul_cancel₀ hnz

private theorem separates_stage (hclosed : ∀ n,
    IsClosedEmbedding (D.transition (Nat.le_succ n))) (m : ℕ) {x : E}
    (hx : x ∉ range (D.incl m)) :
    ∃ g : StrongDual ℂ E, (∀ y, g (D.incl m y) = 0) ∧ g x = 1 := by
  obtain ⟨n, y, rfl⟩ := D.exhaust x
  let k := max m n
  let hm : m ≤ k := le_max_left _ _
  let hn : n ≤ k := le_max_right _ _
  let S := (D.transition hm).toLinearMap.range
  let z := D.transition hn y
  have hz : z ∉ S := by
    rintro ⟨a, ha⟩
    apply hx
    use a
    exact (D.incl_transition hm a).symm.trans
      ((congrArg (D.incl k) ha).trans (D.incl_transition hn y))
  have hS : IsClosed (S : Set (F k)) := (D.all_transitions_closed hclosed hm).isClosed_range
  obtain ⟨f, hzero, hf⟩ := separate_submodule S hS hz
  obtain ⟨g, hg⟩ := D.extend_from_stage (fun j => (hclosed j).isEmbedding) k f
  refine ⟨g, fun a => ?_, ?_⟩
  · rw [← D.incl_transition hm a, hg]
    exact hzero _ ⟨a, rfl⟩
  · rw [← D.incl_transition hn y, hg]
    exact hf

private abbrev BoundedCoordinateSpace := lp (fun _ : ℕ => ℂ) ∞

theorem bounded_preimage_of_embedding {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℂ X] [Module ℂ Y] [TopologicalSpace X] [TopologicalSpace Y]
    (f : X →L[ℂ] Y) (hf : IsEmbedding f) {B : Set Y} (hB : IsVonNBounded ℂ B) :
    IsVonNBounded ℂ (f ⁻¹' B) := by
  intro U hU
  rw [hf.isInducing.nhds_eq_comap, map_zero] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  change ∀ᶠ c : ℂ in cobounded ℂ, f ⁻¹' B ⊆ c • U
  exact (show ∀ᶠ c : ℂ in cobounded ℂ, B ⊆ c • V from hB hV).mono
    (fun c hc x hx => by
      have hx' : f x ∈ B := hx
      obtain ⟨y, hy, he⟩ := hc hx'
      by_cases hz : c = 0
      · subst c
        have hx₀ : x = 0 := hf.injective (by simpa using he.symm)
        subst x
        exact ⟨0, hVU (by simpa using mem_of_mem_nhds hV), zero_smul ℂ (0 : X)⟩
      · refine ⟨c⁻¹ • x, hVU ?_, smul_inv_smul₀ hz x⟩
        change f (c⁻¹ • x) ∈ V
        rwa [map_smul, ← he, inv_smul_smul₀ hz])

/-- In a strict countable inductive limit with closed transition embeddings,
bounded sets are exactly the images of bounded sets in individual stages. -/
theorem strict_bounded_iff
    (hclosed : ∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n)))
    (hemb : ∀ n, IsEmbedding (D.incl n))
    (hlimit : ∀ T : E →ₗ[ℂ] lp (fun _ : ℕ => ℂ) ∞,
      (∀ n, Continuous (T.comp (D.incl n).toLinearMap)) → Continuous T)
    (B : Set E) : IsVonNBounded ℂ B ↔
      ∃ (n : ℕ) (C : Set (F n)), IsVonNBounded ℂ C ∧ D.incl n '' C = B := by
  classical
  constructor
  · intro hB
    have hstage : ∃ n, B ⊆ range (D.incl n) := by
      by_contra! hn
      have hx (n : ℕ) : ∃ x ∈ B, x ∉ range (D.incl n) := by
        simpa only [not_subset] using hn n
      choose x hxB hxoutside using hx
      choose f fzero fone using fun n => D.separates_stage hclosed n (hxoutside n)
      let g (n : ℕ) : StrongDual ℂ E := (n : ℂ) • f n
      have htail {n i : ℕ} (h : n ≤ i) (y : F n) : g i (D.incl n y) = 0 := by
        rw [← D.incl_transition h y]
        change (i : ℂ) * f i (D.incl i (D.transition h y)) = 0
        rw [fzero, mul_zero]
      have hmem (y : E) : Memℓp (fun i => g i y) ∞ := by
        obtain ⟨n, z, rfl⟩ := D.exhaust y
        apply memℓp_infty
        refine ⟨∑ i ∈ Finset.range n, ‖g i (D.incl n z)‖, ?_⟩
        rintro _ ⟨i, rfl⟩
        change ‖g i (D.incl n z)‖ ≤ _
        by_cases hi : i < n
        · exact Finset.single_le_sum (fun j _ => norm_nonneg (g j (D.incl n z))) (Finset.mem_range.mpr hi)
        · rw [htail (le_of_not_gt hi), norm_zero]
          exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      let T : E →ₗ[ℂ] BoundedCoordinateSpace :=
        { toFun := fun y => ⟨fun i => g i y, hmem y⟩
          map_add' := fun y z => lp.ext (funext fun i => (g i).map_add y z)
          map_smul' := fun c y => lp.ext (funext fun i => (g i).map_smul c y) }
      have hT : Continuous T := hlimit T fun n => by
        let truncation : F n →L[ℂ] BoundedCoordinateSpace := ∑ i ∈ Finset.range n,
          (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) ∞ i).comp ((g i).comp (D.incl n))
        have hp : (T.comp (D.incl n).toLinearMap : F n → BoundedCoordinateSpace) = truncation := by
          funext y
          ext i
          change g i (D.incl n y) = (truncation y : BoundedCoordinateSpace) i
          simp only [truncation, sum_apply, lp.coeFn_sum, Finset.sum_apply,
            ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, lp.single_apply,
            Finset.sum_pi_single]
          by_cases hi : i < n
          · simp [Finset.mem_range.mpr hi]
          · simp [Finset.mem_range, hi, htail (le_of_not_gt hi)]
        rw [hp]
        exact truncation.continuous
      have hb := hB.image (⟨T, hT⟩ : E →L[ℂ] BoundedCoordinateSpace)
      obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp hb
      obtain ⟨i, hi⟩ := exists_nat_gt R
      have hvalue : (T (x i) : BoundedCoordinateSpace) i = (i : ℂ) := by
        change (i : ℂ) * f i (x i) = _
        rw [fone, mul_one]
      have hi' := (lp.norm_apply_le_norm ENNReal.top_ne_zero (T (x i)) i).trans
        (hR (T (x i)) ⟨x i, hxB i, rfl⟩)
      rw [hvalue, Complex.norm_natCast] at hi'
      exact (not_le_of_gt hi) hi'
    obtain ⟨n, hn⟩ := hstage
    refine ⟨n, D.incl n ⁻¹' B, bounded_preimage_of_embedding _ (hemb n) hB, ?_⟩
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr hn]
  · rintro ⟨n, C, hC, rfl⟩
    exact hC.image (D.incl n)

/-- The strong-dual isomorphism in the strict closed case. -/
def strongDualRestrictionOfStrict
    (hclosed : ∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n)))
    (hemb : ∀ n, IsEmbedding (D.incl n))
    (hlimit : ∀ T : E →ₗ[ℂ] lp (fun _ : ℕ => ℂ) ∞,
      (∀ n, Continuous (T.comp (D.incl n).toLinearMap)) → Continuous T) :
    StrongDual ℂ E ≃L[ℂ] D.CompatibleDual :=
  D.strongDualRestriction fun B hB => by
    obtain ⟨n, C, hC, he⟩ := (D.strict_bounded_iff hclosed hemb hlimit B).mp hB
    exact ⟨n, C, hC, he.ge⟩

end

end Masullo.LinearInductivePresentation
