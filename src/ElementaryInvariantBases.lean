import ElementarySchwartzSymbols
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Function Module Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

/-- The ordered monomial word with the given multiplicity in each basis direction. -/
def invariantBasisWord {d : ℕ} (a : Fin d → ℕ) : List (Fin d) :=
  (List.ofFn fun j => List.replicate (a j) j).flatten

theorem invariantBasisWord_count {d : ℕ} (a : Fin d → ℕ) (i : Fin d) :
    (invariantBasisWord a).count i = a i := by
  rw [invariantBasisWord, List.count_flatten, List.map_ofFn, List.sum_ofFn]
  simp [List.count_replicate]

theorem invariantBasisWord_perm {d : ℕ} (l : List (Fin d)) :
    l.Perm (invariantBasisWord fun j => l.count j) :=
  List.perm_iff_count.mpr fun i => (invariantBasisWord_count (fun j => l.count j) i).symm

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => ElementarySchwartz m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "Directions" => List (Multiplicative ℝ →ₜ* Multiplicative A)
local notation "Dual" => PontryaginDual (Multiplicative A)

/-- First-order invariant derivatives commute on elementary Schwartz functions. -/
theorem elementarySchwartz_derivative_commute (c d : Multiplicative ℝ →ₜ* Multiplicative A) :
    (elementarySchwartz_derivative c).comp (elementarySchwartz_derivative d) =
      (elementarySchwartz_derivative d).comp (elementarySchwartz_derivative c) := by
  ext f
  apply Subtype.ext
  funext g
  obtain ⟨u, hu⟩ := elementaryOneParameter_lift c
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift d
  obtain ⟨t, ht⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  let x : X := (g.1, t)
  let a := g.2.2.1
  let b := g.2.2.2
  let φ (y : X) := f (elementaryCover y a b)
  have hφ : ContDiff ℝ ∞ φ := f.property.1 a b
  have pair (c₁ c₂ : Multiplicative ℝ →ₜ* Multiplicative A) (u₁ u₂ : X)
      (h₁ : ∀ t : ℝ, (c₁ (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • u₁))
      (h₂ : ∀ t : ℝ, (c₂ (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • u₂)) :
      elementaryOrbitWord [c₁, c₂] f (elementaryCover x a b) =
        iteratedFDeriv ℝ 2 φ x ![u₁, u₂] := by
    have hchoice (i : Fin 2) (t : ℝ) :
        (![c₁, c₂] i (Multiplicative.ofAdd t)).toAdd =
          elementaryCoverHom (t • ![u₁, u₂] i) := by
      fin_cases i
      · exact h₁ t
      · exact h₂ t
    have h := elementaryOrbitWord_tuple ![c₁, c₂] ![u₁, u₂] hchoice f a b hφ x
    simpa only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] using h
  have hs : IsSymmSndFDerivAt ℝ φ x :=
    (hφ.contDiffAt (x := x)).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  change elementaryOrbitWord [c, d] f g = elementaryOrbitWord [d, c] f g
  have heq : elementaryCover x a b = g := ht
  rw [← heq, pair c d u v hu hv, pair d c v u hv hu]
  exact hs.iteratedFDeriv_cons

/-- A word in invariant derivatives depends only on the multiset of directions. -/
theorem elementarySchwartz_derivativeWord_perm {l k : Directions} (h : l.Perm k) :
    elementarySchwartz_derivativeWord l = elementarySchwartz_derivativeWord k := by
  induction h with
  | nil => rfl
  | cons c _ ih =>
    change (elementarySchwartz_derivative c).comp (elementarySchwartz_derivativeWord _) =
      (elementarySchwartz_derivative c).comp (elementarySchwartz_derivativeWord _)
    rw [ih]
  | swap c d l =>
    simp only [elementarySchwartz_derivativeWord, List.foldr_cons]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
      elementarySchwartz_derivative_commute]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- The action on functions of a basis word equals that of the corresponding
ordered monomial. -/
theorem elementaryOrbitWord_basisWord_count {d : ℕ}
    (B : Fin d → Multiplicative ℝ →ₜ* Multiplicative A) (l : List (Fin d)) (f : E) (g : A) :
    elementaryOrbitWord (l.map B) f g =
      elementaryOrbitWord ((invariantBasisWord fun j => l.count j).map B) f g := by
  rw [← elementarySchwartz_derivativeWord_apply, ← elementarySchwartz_derivativeWord_apply,
    elementarySchwartz_derivativeWord_perm ((invariantBasisWord_perm l).map B)]

omit [DiscreteTopology F] in
theorem elementaryDualWord_basisWord_count {d : ℕ}
    (B : Fin d → Multiplicative ℝ →ₜ* Dual) (l : List (Fin d)) (g : A) :
    elementaryDualWord (l.map B) g =
      elementaryDualWord ((invariantBasisWord fun j => l.count j).map B) g :=
  (((invariantBasisWord_perm l).map B).map (fun c => elementaryDualSymbol c g)).prod_eq

/-- Each invariant derivative word is a finite linear combination of
ordered monomials from any real basis of the elementary Lie algebra. -/
theorem elementaryOrbitWord_exists_basisMonomials {d : ℕ}
    (B : Basis (Fin d) ℝ X) (cs : Directions) :
    ∃ P : List (ℂ × (Fin d → ℕ)), ∀ (f : E) (g : A),
      elementaryOrbitWord cs f g = (P.map fun (z, a) =>
        z * elementaryOrbitWord ((invariantBasisWord a).map
          (fun j => elementaryOneParameter (B j))) f g).sum := by
  classical
  choose v hv using fun i : Fin cs.length => elementaryOneParameter_lift (cs.get i)
  let J := Fin cs.length → Fin d
  let e := (Fintype.equivFin J).symm
  let c (j : J) : ℝ := ∏ i, B.repr (v i) (j i)
  let ord (j : J) (i : Fin d) := (List.ofFn j).count i
  let D (j : Fin d) := elementaryOneParameter (r := r) (F := F) (B j)
  refine ⟨List.ofFn (fun i => ((c (e i) : ℂ), ord (e i))), fun f g => ?_⟩
  obtain ⟨t, ht⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  let x : X := (g.1, t)
  let a := g.2.2.1
  let b := g.2.2.2
  let φ (y : X) := f (elementaryCover y a b)
  have hφ : ContDiff ℝ ∞ φ := f.property.1 a b
  let T := iteratedFDeriv ℝ cs.length φ x
  have heq : elementaryCover x a b = g := ht
  rw [← heq, List.map_ofFn, List.sum_ofFn]
  have hinvariant : elementaryOrbitWord cs f (elementaryCover x a b) = T v := by
    simpa only [T, List.ofFn_get] using elementaryOrbitWord_tuple cs.get v hv f a b hφ x
  rw [hinvariant]
  have hword (j : J) :
      T (fun i => B (j i)) =
        elementaryOrbitWord ((invariantBasisWord (ord j)).map D) f (elementaryCover x a b) := by
    have hj := elementaryOrbitWord_tuple (D ∘ j) (fun i => B (j i))
      (fun _ _ => rfl) f a b hφ x
    have hlist : List.ofFn (D ∘ j) = (List.ofFn j).map D := (List.map_ofFn ..).symm
    rw [hlist] at hj
    exact hj.symm.trans (elementaryOrbitWord_basisWord_count D (List.ofFn j) f _)
  have hT : T v = ∑ j : J, c j • T (fun i => B (j i)) := by
    change T.toMultilinearMap v = _
    conv_lhs => rw [show v = (fun i => ∑ j, B.repr (v i) j • B j) from
      funext fun i => (B.sum_repr (v i)).symm]
    rw [T.toMultilinearMap.map_sum]
    simp_rw [T.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe]
    rfl
  rw [hT]
  simp only [comp_apply, hword, Complex.real_smul]
  exact (e.sum_comp _).symm


/-- The one-parameter subgroups on the dual with the given basis coefficients. -/
def elementaryDualBasisDirections {d : ℕ} (B : Basis (Fin d) ℝ ((Fin m ⊕ Fin r) → ℝ))
    (j : Fin d) : Multiplicative ℝ →ₜ* Dual :=
  (elementaryDualSymbol_realizes_realCoefficients (n := n) (F := F) (B j)).choose

theorem elementaryDualBasisDirections_symbol {d : ℕ}
    (B : Basis (Fin d) ℝ ((Fin m ⊕ Fin r) → ℝ)) (j : Fin d) (g : A) :
    elementaryDualSymbol (elementaryDualBasisDirections B j) g =
      Complex.I * ∑ i, (B j i : ℂ) * elementaryGrowthVariables g i :=
  (elementaryDualSymbol_realizes_realCoefficients (n := n) (F := F) (B j)).choose_spec g

omit [DiscreteTopology F] in
private theorem elementaryDualWord_eq_fintype_prod
    (cs : List (Multiplicative ℝ →ₜ* Dual)) (g : A) :
    elementaryDualWord cs g = ∏ i : Fin cs.length, elementaryDualSymbol (cs.get i) g := by
  have h : cs.map (fun c => elementaryDualSymbol c g) =
      List.ofFn (fun i : Fin cs.length => elementaryDualSymbol (cs.get i) g) := by
    change _ = List.ofFn ((fun c => elementaryDualSymbol c g) ∘ cs.get)
    rw [← List.map_ofFn, List.ofFn_get]
  rw [elementaryDualWord, h, List.prod_ofFn]

/-- Each invariant symbol is a finite linear combination of ordered symbols
from any chosen basis of the real Lie algebra of the dual. -/
theorem elementaryDualWord_exists_basisMonomials {d : ℕ}
    (B : Basis (Fin d) ℝ ((Fin m ⊕ Fin r) → ℝ)) (cs : List (Multiplicative ℝ →ₜ* Dual)) :
    ∃ Q : List (ℂ × (Fin d → ℕ)), ∀ g : A,
      elementaryDualWord cs g = (Q.map fun (z, a) =>
        z * elementaryDualWord ((invariantBasisWord a).map (elementaryDualBasisDirections B)) g).sum := by
  classical
  choose v hv using fun i : Fin cs.length => elementaryDualSymbol_exists_realCoefficients (cs.get i)
  let J := Fin cs.length → Fin d
  let e := (Fintype.equivFin J).symm
  let D := elementaryDualBasisDirections (n := n) (F := F) B
  let coeff (i : Fin cs.length) (j : Fin d) : ℂ := (B.repr (v i) j : ℝ)
  let ord (j : J) (i : Fin d) := (List.ofFn j).count i
  refine ⟨List.ofFn (fun i => (∏ k, coeff k (e i k), ord (e i))), fun g => ?_⟩
  have hfirst (i : Fin cs.length) :
      elementaryDualSymbol (cs.get i) g = ∑ j, coeff i j * elementaryDualSymbol (D j) g := by
    rw [hv]
    have he (k : Fin m ⊕ Fin r) : v i k = ∑ j, B.repr (v i) j * B j k := by
      conv_lhs => rw [← B.sum_repr (v i)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [he, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [elementaryDualBasisDirections_symbol B j g]
    simp only [Finset.mul_sum, coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [elementaryDualWord_eq_fintype_prod, List.map_ofFn, List.sum_ofFn]
  simp only [comp_apply, hfirst]
  rw [Fintype.prod_sum]
  have hp (j : J) : (∏ i, elementaryDualSymbol (D (j i)) g) =
      elementaryDualWord ((invariantBasisWord (ord j)).map D) g := by
    rw [← List.prod_ofFn]
    change (List.ofFn ((fun c => elementaryDualSymbol c g) ∘ (D ∘ j))).prod = _
    rw [← List.map_ofFn, ← List.map_ofFn]
    exact elementaryDualWord_basisWord_count D (List.ofFn j) g
  simp only [Finset.prod_mul_distrib, hp]
  exact (e.sum_comp _).symm


end
end Masullo
