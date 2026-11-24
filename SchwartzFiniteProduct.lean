import SchwartzSeparatedDensity

open Function Set
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private def finSchwartzSplit (n : ℕ) : (Fin (n + 1) → V) ≃L[ℝ] V × (Fin n → V) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x 0, Fin.tail x)
      invFun := fun x => Fin.cons x.1 x.2
      left_inv := Fin.cons_self_tail
      right_inv := fun x => by simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The separated Schwartz test with the given coordinate factors. -/
def schwartzFinProduct : ∀ {n : ℕ}, (Fin n → 𝓢(V, ℂ)) → 𝓢(Fin n → V, ℂ)
  | 0, _ => (HasCompactSupport.of_compactSpace (fun _ : Fin 0 → V => (1 : ℂ))).toSchwartzMap
      contDiff_const
  | n + 1, f => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finSchwartzSplit n)
      (schwartzProductLeft (f 0) (schwartzFinProduct (Fin.tail f)))

@[simp] theorem schwartzFinProduct_apply : ∀ {n : ℕ}
    (f : Fin n → 𝓢(V, ℂ)) (x : Fin n → V),
    schwartzFinProduct f x = ∏ i, f i (x i)
  | 0, f, x => by rw [Fin.prod_univ_zero]; rfl
  | n + 1, f, x => by
    rw [Fin.prod_univ_succ]
    change f 0 (x 0) * schwartzFinProduct (Fin.tail f) (Fin.tail x) = _
    rw [schwartzFinProduct_apply]
    rfl

private theorem schwartzFinProduct_cons {n : ℕ} (f : 𝓢(V, ℂ))
    (g : Fin n → 𝓢(V, ℂ)) :
    schwartzFinProduct (Fin.cons f g) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finSchwartzSplit n)
        (schwartzProductLeft f (schwartzFinProduct g)) := by
  simp [schwartzFinProduct]

/-- Continuous functionals on a finite-coordinate Schwartz space are
determined by their values on products of the coordinate tests. -/
theorem schwartzFinFunctional_eq_of_separated {n : ℕ}
    (T U : StrongDual ℂ 𝓢(Fin n → V, ℂ))
    (he : ∀ f, T (schwartzFinProduct f) = U (schwartzFinProduct f)) :
    T = U := by
  induction n with
  | zero =>
    let r := schwartzFinProduct (V := V) (fun i : Fin 0 => i.elim0)
    ext f
    let c := f 0
    have hf : f = c • r := by
      ext x
      rw [show x = 0 from Subsingleton.elim _ _]
      simp [r, c, smul_eq_mul]
    rw [hf, map_smul, map_smul]
    exact congrArg (c • ·) (he _)
  | succ n ih =>
    let e := finSchwartzSplit (V := V) n
    let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
    have hPQ : T.comp P = U.comp P := by
      apply schwartzFunctional_eq_of_separated
      intro f g
      have h := ih ((T.comp P).comp (schwartzProductLeft f))
        ((U.comp P).comp (schwartzProductLeft f)) (fun k => by
          change T (P (schwartzProductLeft f (schwartzFinProduct k))) =
            U (P (schwartzProductLeft f (schwartzFinProduct k)))
          simpa only [schwartzFinProduct_cons] using he (Fin.cons f k))
      exact DFunLike.congr_fun h g
    ext f
    have h : P (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f) = f := by
      ext x
      simp [P]
    rw [← h]
    exact DFunLike.congr_fun hPQ _

/-- Independent coordinate covariance determines every separated pairing
from the value at the product of the reference tests. -/
theorem schwartzFinProduct_eigen_eval {n : ℕ} {I : Type*}
    (A : Fin n → I → 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (w : Fin n → I → ℂ)
    (r : Fin n → 𝓢(V, ℂ)) (N : Fin n → StrongDual ℂ 𝓢(V, ℂ))
    (hN : ∀ (i : Fin n) (U : StrongDual ℂ 𝓢(V, ℂ)),
      (∀ a f, U (A i a f) = w i a * U f) → ∀ f, U f = U (r i) * N i f)
    (T : StrongDual ℂ 𝓢(Fin n → V, ℂ))
    (hT : ∀ i a f,
      T (schwartzFinProduct (update f i (A i a (f i)))) =
        w i a * T (schwartzFinProduct f))
    (f : Fin n → 𝓢(V, ℂ)) :
    T (schwartzFinProduct f) = T (schwartzFinProduct r) * ∏ i, N i (f i) := by
  classical
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero, mul_one]
    exact congrArg (fun g => T (schwartzFinProduct g)) (Subsingleton.elim f r)
  | succ n ih =>
    let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ (finSchwartzSplit (V := V) n)
    let H := (T.comp P).comp (schwartzProductRight (schwartzFinProduct (Fin.tail f)))
    let R := (T.comp P).comp (schwartzProductLeft (r 0))
    have hH (g : 𝓢(V, ℂ)) : H g = T (schwartzFinProduct (Fin.cons g (Fin.tail f))) := by
      have he : schwartzProductRight (schwartzFinProduct (Fin.tail f)) g =
          schwartzProductLeft g (schwartzFinProduct (Fin.tail f)) := by
        ext x
        simp
      simp [H, P, he, schwartzFinProduct_cons]
    have hR (g : Fin n → 𝓢(V, ℂ)) : R (schwartzFinProduct g) =
        T (schwartzFinProduct (Fin.cons (r 0) g)) := by
      simp [R, P, schwartzFinProduct_cons]
    have hhead : H (f 0) = H (r 0) * N 0 (f 0) := by
      apply hN 0 H _ (f 0)
      intro a g
      rw [hH, hH]
      simpa only [Fin.cons_zero, Fin.update_cons_zero] using hT 0 a (Fin.cons g (Fin.tail f))
    have htail : R (schwartzFinProduct (Fin.tail f)) =
        R (schwartzFinProduct (Fin.tail r)) * ∏ i : Fin n, N i.succ (f i.succ) := by
      apply ih (fun i => A i.succ) (fun i => w i.succ) (Fin.tail r) (fun i => N i.succ)
        (fun i => hN i.succ) R _ (Fin.tail f)
      intro i a g
      rw [hR, hR, Fin.cons_update]
      simpa only [Fin.cons_succ] using hT i.succ a (Fin.cons (r 0) g)
    rw [hH, hH, Fin.cons_self_tail, ← hR] at hhead
    rw [hR, hR, Fin.cons_self_tail] at htail
    rw [hhead, hR, htail, Fin.prod_univ_succ]
    ring

variable {ι : Type*} [Fintype ι]

private def schwartzPiCoordinates : (ι → V) ≃L[ℝ] Fin (Fintype.card ι) → V :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ι => V) (Fintype.equivFin ι).symm).symm

omit [FiniteDimensional ℝ V] in
private theorem schwartzPiCoordinates_apply (x : ι → V) (i : Fin (Fintype.card ι)) :
    schwartzPiCoordinates x i = x ((Fintype.equivFin ι).symm i) := rfl

/-- Separated Schwartz tests indexed by an arbitrary finite set. -/
def schwartzPiProduct (f : ι → 𝓢(V, ℂ)) : 𝓢(ι → V, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ schwartzPiCoordinates
    (schwartzFinProduct (f ∘ (Fintype.equivFin ι).symm))

@[simp] theorem schwartzPiProduct_apply (f : ι → 𝓢(V, ℂ)) (x : ι → V) :
    schwartzPiProduct f x = ∏ i, f i (x i) := by
  rw [schwartzPiProduct, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, schwartzFinProduct_apply]
  apply Fintype.prod_equiv (Fintype.equivFin ι).symm
  intro i
  rfl

theorem schwartzPiFunctional_eq_of_separated
    (T U : StrongDual ℂ 𝓢(ι → V, ℂ))
    (he : ∀ f, T (schwartzPiProduct f) = U (schwartzPiProduct f)) : T = U := by
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ (schwartzPiCoordinates (ι := ι) (V := V))
  have h : T.comp P = U.comp P := by
    apply schwartzFinFunctional_eq_of_separated
    intro f
    have he' : (f ∘ Fintype.equivFin ι) ∘ (Fintype.equivFin ι).symm = f := by
      ext i
      simp
    change T (P (schwartzFinProduct f)) = U (P (schwartzFinProduct f))
    simpa only [schwartzPiProduct, he'] using he (f ∘ Fintype.equivFin ι)
  ext f
  have hp : P (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ schwartzPiCoordinates.symm f) = f := by
    ext x
    simp [P]
  rw [← hp]
  exact DFunLike.congr_fun h _

theorem schwartzPiProduct_eigen_eval {I : Type*}
    (A : ι → I → 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (w : ι → I → ℂ)
    (r : ι → 𝓢(V, ℂ)) (N : ι → StrongDual ℂ 𝓢(V, ℂ))
    (hN : ∀ (i : ι) (U : StrongDual ℂ 𝓢(V, ℂ)),
      (∀ a f, U (A i a f) = w i a * U f) → ∀ f, U f = U (r i) * N i f)
    [DecidableEq ι] (T : StrongDual ℂ 𝓢(ι → V, ℂ))
    (hT : ∀ i a f, T (schwartzPiProduct (update f i (A i a (f i)))) =
        w i a * T (schwartzPiProduct f))
    (f : ι → 𝓢(V, ℂ)) :
    T (schwartzPiProduct f) = T (schwartzPiProduct r) * ∏ i, N i (f i) := by
  let e := (Fintype.equivFin ι).symm
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ (schwartzPiCoordinates (ι := ι) (V := V))
  have hp (g : Fin (Fintype.card ι) → 𝓢(V, ℂ)) :
      P (schwartzFinProduct g) = schwartzPiProduct (g ∘ e.symm) := by
    have he : (g ∘ e.symm) ∘ e = g := by ext i; simp
    change _ = P (schwartzFinProduct ((g ∘ e.symm) ∘ e))
    rw [he]
  have h := schwartzFinProduct_eigen_eval (A ∘ e) (w ∘ e) (r ∘ e) (N ∘ e)
    (fun i => hN (e i)) (T.comp P) ?_ (f ∘ e)
  · change _ = T (schwartzPiProduct r) * (∏ i, N i (f i))
    rw [show (∏ i, N i (f i)) = ∏ i, N (e i) (f (e i)) by
      exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm]
    exact h
  · intro i a g
    change T (P (schwartzFinProduct (update g i (A (e i) a (g i))))) =
      w (e i) a * T (P (schwartzFinProduct g))
    rw [hp, hp]
    have hg : (update g i (A (e i) a (g i))) ∘ e.symm =
        update (g ∘ e.symm) (e i) (A (e i) a ((g ∘ e.symm) (e i))) := by
      ext j
      by_cases hj : j = e i
      · subst j
        simp
      · have hne : e.symm j ≠ i := fun h => hj (e.symm_apply_eq.mp h)
        simp [update_of_ne, hj, hne]
    rw [hg]
    exact hT (e i) a (g ∘ e.symm)

end
end Masullo
