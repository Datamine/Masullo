import SchwartzFiniteProduct
import ComplexPuncturedWeilEigen

open Function NumberField
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev E := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

def mixedWeilTest (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) : E F :=
  schwartzProductLeft (schwartzPiProduct f) (schwartzPiProduct g)

@[simp] theorem mixedWeilTest_apply (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (x : mixedEmbedding.mixedSpace F) :
    mixedWeilTest F f g x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v) := by
  simp [mixedWeilTest]

theorem mixedWeilFunctional_eq_of_separated (T U : StrongDual ℂ (E F))
    (he : ∀ f g, T (mixedWeilTest F f g) = U (mixedWeilTest F f g)) : T = U := by
  apply schwartzFunctional_eq_of_separated
  intro φ ψ
  have h (g : C F → 𝓢(ℂ, ℂ)) :
      T (schwartzProductRight (schwartzPiProduct g) φ) =
        U (schwartzProductRight (schwartzPiProduct g) φ) := by
    apply DFunLike.congr_fun (f := T.comp (schwartzProductRight (schwartzPiProduct g)))
      (g := U.comp (schwartzProductRight (schwartzPiProduct g))) _ φ
    apply schwartzPiFunctional_eq_of_separated
    intro f
    have hprod : schwartzProductRight (schwartzPiProduct g) (schwartzPiProduct f) =
        mixedWeilTest F f g := by ext x; simp
    exact (congrArg T hprod).trans ((he f g).trans (congrArg U hprod.symm))
  have h' : T.comp (schwartzProductLeft φ) = U.comp (schwartzProductLeft φ) := by
    apply schwartzPiFunctional_eq_of_separated
    intro g
    have hprod : schwartzProductLeft φ (schwartzPiProduct g) =
        schwartzProductRight (schwartzPiProduct g) φ := by ext x; simp
    exact (congrArg T hprod).trans ((h g).trans (congrArg U hprod.symm))
  exact DFunLike.congr_fun h' ψ

def mixedWeilRealReference (a : R F → ℂ × ℕ) (v : R F) : 𝓢(ℝ, ℂ) :=
  (realGammaNormalized_distribution (a v).2).choose

def mixedWeilComplexReference (j : C F → ℂ × ℤ) (v : C F) : 𝓢(ℂ, ℂ) :=
  (complexGammaNormalized_distribution (j v).2).choose

/-- The real and complex classifications give the pairing against the entire
archimedean separated test from the single product reference. -/
theorem mixedWeilEigen_eval
    (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ) (z : ℂ)
    (T : StrongDual ℂ (E F))
    (hR : ∀ v u f g, T (mixedWeilTest F (update f v (archSchwartzDilation u (f v))) g) =
      realArchUnitWeight (a v).2 (z + (a v).1) u * T (mixedWeilTest F f g))
    (hC : ∀ v u f g, T (mixedWeilTest F f (update g v (archSchwartzDilation u (g v)))) =
      complexArchUnitWeight (j v).2 (z + (j v).1) u * T (mixedWeilTest F f g))
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
    T (mixedWeilTest F f g) =
      T (mixedWeilTest F (mixedWeilRealReference F a) (mixedWeilComplexReference F j)) *
        ((∏ v, realWeilNormalizedFamily (a v).2 (z + (a v).1) (f v)) *
         ∏ v, complexWeilNormalizedFamily (j v).2 (z + (j v).1) (g v)) := by
  let r := mixedWeilRealReference F a
  let s := mixedWeilComplexReference F j
  let L (v : R F) := realWeilNormalizedFamily (a v).2 (z + (a v).1)
  let M (v : C F) := complexWeilNormalizedFamily (j v).2 (z + (j v).1)
  let A := T.comp (schwartzProductRight (schwartzPiProduct g))
  let B := T.comp (schwartzProductLeft (schwartzPiProduct r))
  have hA (k : R F → 𝓢(ℝ, ℂ)) : A (schwartzPiProduct k) = T (mixedWeilTest F k g) := by
    apply congrArg T
    ext x
    simp
  have hB (k : C F → 𝓢(ℂ, ℂ)) : B (schwartzPiProduct k) = T (mixedWeilTest F r k) := rfl
  have hL (v : R F) (U : StrongDual ℂ 𝓢(ℝ, ℂ))
      (hU : ∀ u q, U (archSchwartzDilation u q) = realArchUnitWeight (a v).2 (z + (a v).1) u * U q)
      (q : 𝓢(ℝ, ℂ)) : U q = U (r v) * L v q := by
    obtain ⟨c, hc⟩ := realWeilEigen_eq_normalized U (a v).2 (z + (a v).1) hU
    have h1 : L v (r v) = 1 :=
      (realGammaNormalized_distribution (a v).2).choose_spec.choose_spec.2.2.1 _
    rw [hc]
    change c * L v q = (c * L v (r v)) * L v q
    rw [h1, mul_one]
  have hM (v : C F) (U : StrongDual ℂ 𝓢(ℂ, ℂ))
      (hU : ∀ u q, U (archSchwartzDilation u q) = complexArchUnitWeight (j v).2 (z + (j v).1) u * U q)
      (q : 𝓢(ℂ, ℂ)) : U q = U (s v) * M v q := by
    obtain ⟨c, hc⟩ := complexWeilEigen_eq_normalized U (j v).2 (z + (j v).1) hU
    have h1 : M v (s v) = 1 :=
      (complexGammaNormalized_distribution (j v).2).choose_spec.choose_spec.2.2.1 _
    rw [hc]
    change c * M v q = (c * M v (s v)) * M v q
    rw [h1, mul_one]
  have hr := schwartzPiProduct_eigen_eval (fun _ => archSchwartzDilation)
    (fun v => realArchUnitWeight (a v).2 (z + (a v).1)) r L hL A
      (fun v u k => by simp only [hA]; exact hR v u k g) f
  have hs := schwartzPiProduct_eigen_eval (fun _ => archSchwartzDilation)
    (fun v => complexArchUnitWeight (j v).2 (z + (j v).1)) s M hM B
      (fun v u k => by simp only [hB]; exact hC v u r k) g
  simp only [hA, hB] at hr hs
  rw [hr, hs]
  change (T (mixedWeilTest F r s) * (∏ v, M v (g v))) * (∏ v, L v (f v)) =
    T (mixedWeilTest F r s) * ((∏ v, L v (f v)) * ∏ v, M v (g v))
  ring

end
end Masullo
