import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

open Filter Function Set Topology
open scoped Pointwise ComplexOrder

namespace Masullo

noncomputable section

variable {E Z : Type*} {F : ℕ → Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)] [∀ n, TopologicalSpace (F n)]
variable [∀ n, IsTopologicalAddGroup (F n)] [∀ n, ContinuousSMul ℂ (F n)]
variable [∀ n, LocallyConvexSpace ℂ (F n)]
variable [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]

/-- A countable locally convex inductive limit tests continuity of linear
maps into any topological vector space. The seminorm criterion is the part
of the locally convex universal property needed in the proof. -/
theorem continuous_of_countable_stage_restrictions (j : ∀ n, F n →L[ℂ] E)
    (hexhaust : ∀ x : E, ∃ n, x ∈ range (j n))
    (hseminorm : ∀ p : Seminorm ℂ E,
      (∀ n, Continuous (p.comp (j n).toLinearMap)) → Continuous p)
    (L : E →ₗ[ℂ] Z) (hL : ∀ n, Continuous (L.comp (j n).toLinearMap)) : Continuous L := by
  letI : Module ℝ E := Module.restrictScalars ℝ ℂ E
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  letI (n : ℕ) : Module ℝ (F n) := Module.restrictScalars ℝ ℂ (F n)
  letI (n : ℕ) : IsScalarTower ℝ ℂ (F n) := IsScalarTower.restrictScalars ℝ ℂ (F n)
  letI (n : ℕ) : ContinuousSMul ℝ (F n) := IsScalarTower.continuousSMul (M := ℝ) (α := F n) ℂ
  refine continuous_of_tendsto_nhds_zero (G := E) (M := Z) L.toAddMonoidHom ?_
  apply tendsto_def.mpr
  intro U hU
  let step (V : {V : Set Z // V ∈ 𝓝 (0 : Z)}) :=
    exists_closed_nhds_zero_neg_eq_add_subset V.property
  let v : ℕ → {V : Set Z // V ∈ 𝓝 (0 : Z)} := Nat.rec ⟨U, hU⟩ fun _ V =>
    ⟨(step V).choose, (step V).choose_spec.1⟩
  have hvadd (n : ℕ) : (v (n + 1)).val + (v (n + 1)).val ⊆ (v n).val :=
    (step (v n)).choose_spec.2.2.2
  have hstage (n : ℕ) : ∃ s : Set (F n), (0 ∈ s ∧ IsOpen s ∧ AbsConvex ℂ s) ∧
      s ⊆ (L.comp (j n).toLinearMap) ⁻¹' (v (n + 1)).val := by
    have hp := (hL n).continuousAt.preimage_mem_nhds (x := 0)
      (show (v (n + 1)).val ∈ 𝓝 ((L.comp (j n).toLinearMap) 0) from by simp [(v (n + 1)).property])
    exact (nhds_hasBasis_absConvex_open ℂ (F n)).mem_iff.mp hp
  choose b hb hmap using hstage
  let T (m n : ℕ) : Set E :=
    Nat.rec (motive := fun _ => ℕ → Set E) (fun _ => {0})
      (fun _ tail m => j m '' b m + tail (m + 1)) n m
  have hzero (m n : ℕ) : 0 ∈ T m n := by
    induction n generalizing m with
    | zero => rfl
    | succ n ih =>
      exact ⟨j m 0, ⟨0, (hb m).1, rfl⟩, 0, ih (m + 1), by simp⟩
  have hTmono (m : ℕ) : Monotone (T m) := by
    apply monotone_nat_of_le_succ
    intro n
    induction n generalizing m with
    | zero =>
      change ({0} : Set E) ⊆ T m 1
      exact singleton_subset_iff.mpr (hzero m 1)
    | succ n ih =>
      change j m '' b m + T (m + 1) n ⊆ j m '' b m + T (m + 1) (n + 1)
      exact add_subset_add Subset.rfl (ih (m + 1))
  have hAbs (m n : ℕ) : AbsConvex ℂ (T m n) := by
    induction n generalizing m with
    | zero => exact ⟨balanced_zero, convex_singleton 0⟩
    | succ n ih =>
      change AbsConvex ℂ (j m '' b m + T (m + 1) n)
      refine ⟨Balanced.add ?_ (ih _).1, Convex.add ?_ (ih _).2⟩
      · intro c hc y hy
        obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy
        exact ⟨c • x, (hb m).2.2.1.smul_mem hc hx, map_smul (j m) c x⟩
      · exact (hb m).2.2.2.linear_image (j m).toLinearMap
  have hTmap (m n : ℕ) : T m n ⊆ L ⁻¹' (v m).val := by
    induction n generalizing m with
    | zero =>
      rintro _ (rfl : _ = 0)
      simpa using mem_of_mem_nhds (v m).property
    | succ n ih =>
      rintro _ ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
      change L (j m a + z) ∈ (v m).val
      rw [map_add]
      exact hvadd m ⟨_, hmap m ha, _, ih (m + 1) hz, rfl⟩
  let C : Set E := ⋃ n, T 0 n
  have hCin (m : ℕ) : j m '' b m ⊆ C := by
    have htail (k d : ℕ) : j (d + k) '' b (d + k) ⊆ T k (d + 1) := by
      induction d generalizing k with
      | zero =>
        intro x hx
        rw [Nat.zero_add] at hx
        exact ⟨x, hx, 0, hzero (k + 1) 0, add_zero _⟩
      | succ d ih =>
        intro x hx
        have he : d + 1 + k = d + (k + 1) := by omega
        rw [he] at hx
        exact ⟨j k 0, ⟨0, (hb k).1, rfl⟩, x, ih (k + 1) hx, by simp⟩
    exact (htail 0 m).trans (subset_iUnion _ _)
  have hCU : C ⊆ L ⁻¹' U := iUnion_subset (hTmap 0)
  have hCbal : Balanced ℂ C := balanced_iUnion fun n => (hAbs 0 n).1
  have hCconv : Convex ℝ C := (hTmono 0).directed_le.convex_iUnion fun n => (hAbs 0 n).2.lift ℝ
  have hCabs : Absorbent ℝ C := by
    apply absorbent_iff_inv_smul.mpr
    intro x
    obtain ⟨n, y, rfl⟩ := hexhaust x
    have h := absorbent_iff_inv_smul.mp
      (absorbent_nhds_zero (𝕜 := ℝ) ((hb n).2.1.mem_nhds (hb n).1)) y
    filter_upwards [h] with c hc
    have he : j n (c⁻¹ • y) = c⁻¹ • j n y := ((j n).toLinearMap.restrictScalars ℝ).map_smul c⁻¹ y
    exact hCin n ⟨c⁻¹ • y, hc, he⟩
  let p := gaugeSeminorm hCbal hCconv hCabs
  have hp : Continuous p := hseminorm p fun n => by
    apply Seminorm.continuous (r := 2)
    refine mem_of_superset ((hb n).2.1.mem_nhds (hb n).1) fun x hx => ?_
    rw [Seminorm.ball_zero_eq]
    change (p.comp (j n).toLinearMap) x < 2
    exact (gauge_le_one_of_mem (hCin n ⟨x, hx, rfl⟩)).trans_lt (by norm_num)
  refine mem_of_superset (hp.continuousAt.preimage_mem_nhds (x := 0)
    (show Iio (1 : ℝ) ∈ 𝓝 (p 0) from by simpa using Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))) ?_
  intro x hx
  exact hCU (setOfPred_gauge_lt_one_subset_self hCconv hCabs.zero_mem hCabs hx)

end

end Masullo
