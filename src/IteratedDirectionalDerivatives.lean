import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

open Function
open scoped ContDiff ENat

namespace Masullo

noncomputable section

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Take derivatives in a list of constant directions, with the head outermost. -/
def iteratedDirectionalDerivative : List X → (X → V) → X → V
  | [], f => f
  | v :: l, f => fun x => fderiv ℝ (iteratedDirectionalDerivative l f) x v

theorem contDiff_iteratedDirectionalDerivative (l : List X) {f : X → V}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (iteratedDirectionalDerivative l f) := by
  induction l with
  | nil => exact hf
  | cons v l ih =>
    exact ((ih.fderiv_right (by simp)).clm_apply contDiff_const)

private theorem fderiv_fderiv_fixed_apply {g : X → V} (hg : ContDiff ℝ ∞ g)
    (x v w : X) :
    fderiv ℝ (fun y => fderiv ℝ g y w) x v = fderiv ℝ (fderiv ℝ g) x v w := by
  have h := hg.fderiv_right (m := (1 : ℕ∞ω)) (WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x := h.differentiable one_ne_zero x
  let e := ContinuousLinearMap.apply ℝ V w
  have he := e.hasFDerivAt.comp x hd.hasFDerivAt
  exact congrFun (congrArg DFunLike.coe he.fderiv) v

/-- Reordering a list of constant directions preserves the mixed derivative of a smooth function. -/
theorem iteratedDirectionalDerivative_perm {a b : List X} (hab : a.Perm b)
    {f : X → V} (hf : ContDiff ℝ ∞ f) :
    iteratedDirectionalDerivative a f = iteratedDirectionalDerivative b f := by
  induction hab with
  | nil => rfl
  | cons v h ih => simp only [iteratedDirectionalDerivative, ih]
  | swap v w l =>
    let g := iteratedDirectionalDerivative l f
    have hg : ContDiff ℝ ∞ g := contDiff_iteratedDirectionalDerivative l hf
    funext x
    change fderiv ℝ (fun y => fderiv ℝ g y v) x w =
      fderiv ℝ (fun y => fderiv ℝ g y w) x v
    rw [fderiv_fderiv_fixed_apply hg, fderiv_fderiv_fixed_apply hg]
    exact (hg.contDiffAt.isSymmSndFDerivAt (by
      simpa [minSmoothness] using (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))).eq w v
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An iterated Fréchet derivative entry equals the corresponding repeated directional derivative. -/
theorem iteratedDirectionalDerivative_ofFn {f : X → V} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → X) (x : X) :
    iteratedDirectionalDerivative (List.ofFn v) f x = iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => rw [List.ofFn_zero]; exact (iteratedFDeriv_zero_apply _).symm
  | succ n ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (iteratedDirectionalDerivative (List.ofFn (Fin.tail v)) f) x (v 0) = _
    rw [funext (ih (Fin.tail v))]
    exact ((hf.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x).iteratedFDeriv_succ_apply_left'
        (m := v)).symm

/-- Every iterated Fréchet derivative of a smooth real map is symmetric. -/
theorem iteratedFDeriv_apply_perm {f : X → V} (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → X) (x : X) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  rw [← iteratedDirectionalDerivative_ofFn hf, ← iteratedDirectionalDerivative_ofFn hf]
  exact congrFun (iteratedDirectionalDerivative_perm (σ.ofFn_comp_perm v) hf) x

/-- A distinguished direction may move from the front to the back of the list. -/
theorem iteratedFDeriv_apply_cons_eq_snoc {f : X → V} (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (v : X) (m : Fin n → X) (x : X) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons v m) =
      iteratedFDeriv ℝ (n + 1) f x (Fin.snoc m v) := by
  rw [← iteratedDirectionalDerivative_ofFn hf, ← iteratedDirectionalDerivative_ofFn hf,
    List.ofFn_succ, List.ofFn_succ_last]
  simpa only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_last, Fin.snoc_castSucc] using
    congrFun (iteratedDirectionalDerivative_perm
      (List.perm_append_singleton (a := v) (l := List.ofFn m)).symm hf) x

/-- Differentiating in one direction commutes with taking any mixed derivative entries. -/
theorem iteratedFDeriv_directional_apply {f : X → V} (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (v : X) (m : Fin n → X) (x : X) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x m =
      iteratedFDeriv ℝ (n + 1) f x (Fin.cons v m) := by
  let L := ContinuousLinearMap.apply ℝ V v
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  change iteratedFDeriv ℝ n (L ∘ fderiv ℝ f) x m = _
  rw [L.iteratedFDeriv_comp_left hDf.contDiffAt (WithTop.coe_le_coe.mpr le_top),
    iteratedFDeriv_apply_cons_eq_snoc hf,
    iteratedFDeriv_succ_apply_right]
  simp [L, Fin.init_snoc]


end
end Masullo
