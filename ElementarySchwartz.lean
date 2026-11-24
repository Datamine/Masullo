/-
Adapted from the Apache-2.0 RiemannMasullo project at
3b4b2cd6915a243a5299a26001ca6b1c1a2ed037, AppD_SchwartzBruhat/Sec1a.lean
and its covering and derivative permutation lemmas.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import ElementaryLCAStructure
import SchwartzBergman
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.InnerProductSpace.PiL2

open Bornology Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

/-- A continuous homomorphism from a simply connected, locally path-connected
topological additive group to the circle lifts to a continuous real-valued homomorphism. -/
theorem exists_addCircle_addMonoidHom_lift {A : Type*} [AddGroup A] [TopologicalSpace A]
    [ContinuousAdd A] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (a : A →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ L : A →+ ℝ, Continuous L ∧ ∀ x, (L x : AddCircle (1 : ℝ)) = a x := by
  let q : ℝ → AddCircle (1 : ℝ) := (↑)
  have hq : IsCoveringMap q := AddCircle.isCoveringMap_coe _
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    (⟨a, ha⟩ : C(A, AddCircle (1 : ℝ))) 0 0 (by simp [q])
  have hLift (t : A) : q (L t) = a t := congrFun hL t
  have hAdd (s t : A) : L (s + t) = L s + L t := by
    have hAgree : q ∘ (fun p : A × A ↦ L (p.1 + p.2)) =
        q ∘ (fun p : A × A ↦ L p.1 + L p.2) := by
      funext p
      change q (L (p.1 + p.2)) = ((L p.1 + L p.2 : ℝ) : AddCircle (1 : ℝ))
      rw [AddCircle.coe_add]
      change q (L (p.1 + p.2)) = q (L p.1) + q (L p.2)
      simp only [hLift, map_add]
    exact congrFun (hq.eq_of_comp_eq (L.continuous.comp (continuous_fst.add continuous_snd))
      ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
      hAgree (0, 0) (by simp [hL0])) (s, t)
  exact ⟨{ toFun := L, map_zero' := hL0, map_add' := hAdd }, L.continuous, hLift⟩

private theorem finiteOrder_le_smoothOrder (k : ℕ) : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl k

private theorem smoothOrder_add_finite (k : ℕ) :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  change ((⊤ : ℕ∞) : WithTop ℕ∞) + ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  rw [← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr le_top

/-- Permuting a list of directions leaves the iterated derivative of a smooth real map unchanged. -/
theorem iteratedFDeriv_apply_list_perm {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (v : ι → E) {l r : List ι} (h : l.Perm r) (x : E) :
    iteratedFDeriv ℝ l.length f x (fun i ↦ v (l.get i)) =
      iteratedFDeriv ℝ r.length f x (fun i ↦ v (r.get i)) := by
  let D (s : List ι) (y : E) := iteratedFDeriv ℝ s.length f y (fun i ↦ v (s.get i))
  have hs (s : List ι) : ContDiff ℝ ∞ (D s) :=
    (ContinuousMultilinearMap.apply ℝ _ F (fun i ↦ v (s.get i))).contDiff.comp
      (hf.iteratedFDeriv_right (smoothOrder_add_finite _))
  have hcons (i : ι) (s : List ι) : D (i :: s) = fun y ↦ fderiv ℝ (D s) y (v i) := by
    funext y
    have hy := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top s.length) y
    exact hy.iteratedFDeriv_succ_apply_left' (m := fun j ↦ v ((i :: s).get j))
  suffices D l = D r from congrFun this x
  induction h with
  | nil => rfl
  | cons i h ih => rw [hcons, hcons, ih]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap i j s =>
    funext y
    have hder (a b : ι) :
        fderiv ℝ (fun z ↦ fderiv ℝ (D s) z (v b)) y (v a) =
          fderiv ℝ (fderiv ℝ (D s)) y (v a) (v b) := by
      let ev := ContinuousLinearMap.apply ℝ F (v b)
      have hdiff := ((hs s).fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
      exact congrArg (fun t : E →L[ℝ] F ↦ t (v a))
        (ev.hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv
    simp only [hcons, hder]
    exact ((hs s).contDiffAt.isSymmSndFDerivAt (by simpa using finiteOrder_le_smoothOrder 2)).eq _ _

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

/-- Paper: (D.1.3.2), p. 749. The covering map reduces each real torus coordinate
modulo the integer lattice and leaves the other coordinates fixed. -/
def elementaryCover (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a : Fin r → ℤ) (b : F) : ElementaryLCAModel m n r F :=
  (xt.1, fun i ↦ (xt.2 i : AddCircle (1 : ℝ)), a, b)

/-- The additive homomorphism covering the real and torus coordinates. -/
def elementaryCoverHom :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →+ ElementaryLCAModel m n r F where
  toFun u := elementaryCover u 0 0
  map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
  map_add' u v := Prod.ext rfl
    (Prod.ext (funext fun i ↦ AddCircle.coe_add 1 (u.2 i) (v.2 i)) (zero_add _).symm)

omit [DiscreteTopology F] [Finite F] in
theorem elementaryCoverHom_continuous : Continuous (elementaryCoverHom (m := m) (n := n)
    (r := r) (F := F)) :=
  continuous_fst.prodMk
    ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk
        (continuous_const.prodMk continuous_const))

omit [DiscreteTopology F] [Finite F] in
theorem elementaryCover_add (u v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a : Fin r → ℤ) (b : F) :
    elementaryCover (u + v) a b = elementaryCover u a b + elementaryCoverHom v := by
  refine Prod.ext rfl (Prod.ext (funext fun i ↦ AddCircle.coe_add 1 (u.2 i) (v.2 i)) ?_)
  change (a, b) = (a + 0, b + 0)
  rw [add_zero, add_zero]

/-- Paper: (D.1.3.1)–(D.1.3.2), p. 749. Every group element has a lift
for its real and torus coordinates. -/
theorem elementaryCover_surjective (a : Fin r → ℤ) (b : F)
    (x : EuclideanSpace ℝ (Fin m)) (z : Fin n → AddCircle (1 : ℝ)) :
    ∃ t : EuclideanSpace ℝ (Fin n), elementaryCover (x, t) a b = (x, z, a, b) := by
  choose s hs using fun i ↦ QuotientAddGroup.mk_surjective (z i)
  refine ⟨WithLp.toLp 2 s, ?_⟩
  simp only [elementaryCover, Prod.mk.injEq, true_and, and_true]
  funext i
  exact hs i

/-- Paper: (D.1.3.3), p. 749. The mixed partial is evaluated on the cover by
repeating differentiation along each coordinate vector according to its exponent. -/
def elementaryPartial (f : ElementaryLCAModel m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) : ℂ :=
  let realDirections : List (List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    List.ofFn (fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))
  let torusDirections : List (List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    List.ofFn (fun i : Fin n ↦ List.replicate (γ i) (0, EuclideanSpace.single i 1))
  let directions : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    realDirections.flatten ++ torusDirections.flatten
  iteratedFDeriv ℝ directions.length (fun v ↦ f (elementaryCover v a b)) xt directions.get

/-- Paper: (D.1.3.3), p. 749. With both multi-indices zero, the partial is just the
pullback of the function to the cover. -/
theorem elementaryPartial_zero (f : ElementaryLCAModel m n r F → ℂ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial f 0 0 xt a b = f (elementaryCover xt a b) := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let directions : List X :=
    ((List.ofFn (fun _ : Fin m ↦ ([] : List X))).flatten ++
      (List.ofFn (fun _ : Fin n ↦ ([] : List X))).flatten)
  have hnil (k : ℕ) : (List.replicate k ([] : List X)).flatten = [] := by
    induction k with
    | zero => rfl
    | succ j ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl
  have hdir : directions = [] := by
    dsimp [directions]
    rw [List.ofFn_const, List.ofFn_const]
    rw [hnil m, hnil n]
    rfl
  have hlen : directions.length = 0 := by rw [hdir]; rfl
  simp only [elementaryPartial]
  change (iteratedFDeriv ℝ directions.length (fun v ↦ f (elementaryCover v a b)) xt)
      directions.get = f (elementaryCover xt a b)
  have hiter (k : ℕ) (hk : k = 0) (d : Fin k → X) :
      (iteratedFDeriv ℝ k (fun v ↦ f (elementaryCover v a b)) xt) d =
        f (elementaryCover xt a b) := by
    subst k
    exact iteratedFDeriv_zero_apply d
  exact hiter directions.length hlen directions.get

/-- Paper: (D.1.3.4), p. 750. The lifted partials of a smooth fibre are smooth
and have the same value at any two lifts of a given group point. -/
theorem elementaryPartial_descends (f : ElementaryLCAModel m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) :
    ContDiff ℝ ∞ (fun xt ↦ elementaryPartial f β γ xt a b) ∧
      ∀ u v, elementaryCover u a b = elementaryCover v a b →
        elementaryPartial f β γ u a b = elementaryPartial f β γ v a b := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let p : X → ℂ := fun w ↦ f (elementaryCover w a b)
  have hs {k : ℕ} (d : Fin k → X) :
      ContDiff ℝ ∞ (fun w ↦ (iteratedFDeriv ℝ k p w) d) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ X) ℂ d).contDiff.comp
      (hf.iteratedFDeriv_right (smoothOrder_add_finite _))
  refine ⟨hs _, fun u v huv ↦ ?_⟩
  have hre : u.1 = v.1 := congrArg (fun y : ElementaryLCAModel m n r F ↦ y.1) huv
  have htor (i : Fin n) : (u.2 i : AddCircle (1 : ℝ)) = (v.2 i : AddCircle (1 : ℝ)) :=
    congrArg (fun y : ElementaryLCAModel m n r F ↦ y.2.1 i) huv
  have hshift : (fun w : X ↦ p (w + (v - u))) = p := by
    funext w
    apply congrArg f
    apply Prod.ext
    · change w.1 + (v.1 - u.1) = w.1
      simp [hre]
    · refine Prod.ext (funext fun i ↦ ?_) rfl
      change ((w.2 i + (v.2 i - u.2 i) : ℝ) : AddCircle (1 : ℝ)) = (w.2 i : AddCircle (1 : ℝ))
      simp only [AddCircle.coe_add, AddCircle.coe_sub, htor, sub_self, add_zero]
  have hderiv (k : ℕ) : iteratedFDeriv ℝ k p u = iteratedFDeriv ℝ k p v := by
    simpa only [hshift, add_sub_cancel] using
      (iteratedFDeriv_comp_add_right (f := p) k (v - u) u)
  dsimp only [elementaryPartial]
  dsimp only [p] at hderiv
  rw [hderiv]

/-- Paper: (D.1.3.7), p. 750. These are the two monomial multi-indices and the
two derivative multi-indices in the paper's order. -/
abbrev ElementarySchwartzIndex (m n r : ℕ) :=
  (Fin m → ℕ) × (Fin m → ℕ) × (Fin n → ℕ) × (Fin r → ℕ)

/-- Paper: (D.1.3.6)–(D.1.3.7), p. 750. Take the supremum of the absolute value
of a mixed partial multiplied by the real and integer monomials.
Deviation: The supremum ranges over all lifts of the torus coordinates. -/
def elementarySchwartzBound (f : ElementaryLCAModel m n r F → ℂ)
    (i : ElementarySchwartzIndex m n r) : ℝ≥0∞ :=
  ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
    ((‖((∏ k, (xt.1 k : ℂ) ^ i.1 k) * (∏ k, (a k : ℂ) ^ i.2.2.2 k)) *
      elementaryPartial f i.2.1 i.2.2.1 xt a b‖₊ : ℝ≥0∞))

/-- Paper: (D.1.3.7), p. 750. With every index zero the bound is the supremum
of the absolute value of the original function. -/
theorem elementarySchwartzBound_zero (f : ElementaryLCAModel m n r F → ℂ) :
    elementarySchwartzBound f (0, 0, 0, 0) =
      ⨆ g, (‖f g‖₊ : ℝ≥0∞) := by
  simp only [elementarySchwartzBound, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul,
    elementaryPartial_zero]
  apply le_antisymm
  · exact iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ le_iSup (fun g ↦ (‖f g‖₊ : ℝ≥0∞)) (elementaryCover xt a b)
  · refine iSup_le fun ⟨x, z, a, b⟩ ↦ ?_
    obtain ⟨t, ht⟩ := elementaryCover_surjective a b x z
    rw [← ht]
    exact le_iSup_of_le (x, t) (le_iSup_of_le a (le_iSup_of_le b le_rfl))

section

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Paper: Definition D.1.3.1, p. 750. The zero function is smooth on each
discrete fibre and has finite weighted bounds. -/
theorem elementarySchwartzSubmodule_zero_mem :
    (0 : ElementaryLCAModel m n r F → ℂ) ∈
      {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
        ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)} := by
  refine ⟨fun _ _ ↦ contDiff_const, fun i ↦ ?_⟩
  simp [elementarySchwartzBound, elementaryPartial]

/-- Each weighted mixed-derivative bound is subadditive on fibrewise smooth functions. -/
theorem elementarySchwartzBound_add_le {f g : ElementaryLCAModel m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (hg : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b)))
    (i : ElementarySchwartzIndex m n r) :
    elementarySchwartzBound (f + g) i ≤ elementarySchwartzBound f i + elementarySchwartzBound g i := by
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have hpartial : elementaryPartial (f + g) i.2.1 i.2.2.1 xt a b =
      elementaryPartial f i.2.1 i.2.2.1 xt a b + elementaryPartial g i.2.1 i.2.2.1 xt a b := by
    have hadd (n : ℕ) :
        iteratedFDeriv ℝ n (fun v ↦ (f + g) (elementaryCover v a b)) xt =
          iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt +
          iteratedFDeriv ℝ n (fun v ↦ g (elementaryCover v a b)) xt :=
      iteratedFDeriv_add_apply ((hf a b).of_le (finiteOrder_le_smoothOrder n)).contDiffAt
        ((hg a b).of_le (finiteOrder_le_smoothOrder n)).contDiffAt
    dsimp only [elementaryPartial]
    rw [hadd]
    rfl
  rw [hpartial, mul_add]
  refine le_trans (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)) ?_
  rw [ENNReal.coe_add]
  apply add_le_add <;> exact le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))

/-- Paper: Definition D.1.3.1, p. 750. The Schwartz condition is closed under addition. -/
theorem elementarySchwartzSubmodule_add_mem {f g : ElementaryLCAModel m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞))
    (hg : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) :
    f + g ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by
  refine ⟨fun a b ↦ (hf.1 a b).add (hg.1 a b), fun i ↦ ?_⟩
  exact (elementarySchwartzBound_add_le hf.1 hg.1 i).trans_lt (ENNReal.add_lt_top.2 ⟨hf.2 i, hg.2 i⟩)

/-- Complex scalar multiplication scales each weighted mixed-derivative bound by its norm. -/
theorem elementarySchwartzBound_smul (c : ℂ) {f : ElementaryLCAModel m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (i : ElementarySchwartzIndex m n r) :
    elementarySchwartzBound (c • f) i = (‖c‖₊ : ℝ≥0∞) * elementarySchwartzBound f i := by
  simp only [elementarySchwartzBound, ENNReal.mul_iSup]
  apply iSup_congr
  intro xt
  apply iSup_congr
  intro a
  apply iSup_congr
  intro b
  have hpartial : elementaryPartial (c • f) i.2.1 i.2.2.1 xt a b =
      c • elementaryPartial f i.2.1 i.2.2.1 xt a b := by
    have hsmul (n : ℕ) :
        iteratedFDeriv ℝ n (fun v ↦ (c • f) (elementaryCover v a b)) xt =
          c • iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt :=
      iteratedFDeriv_const_smul_apply ((hf a b).of_le (finiteOrder_le_smoothOrder n)).contDiffAt
    dsimp only [elementaryPartial]
    rw [hsmul]
    rfl
  rw [hpartial, smul_eq_mul, mul_left_comm, nnnorm_mul, ENNReal.coe_mul]

/-- Paper: Definition D.1.3.1, p. 750. The Schwartz condition is closed under
complex scalar multiplication. -/
theorem elementarySchwartzSubmodule_smul_mem (c : ℂ) {f : ElementaryLCAModel m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)) :
    c • f ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by
  refine ⟨fun a b ↦ (hf.1 a b).const_smul c, fun i ↦ ?_⟩
  rw [elementarySchwartzBound_smul c hf.1 i]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hf.2 i)

/-- Paper: Definition D.1.3.1, p. 750. A Schwartz function is smooth in the real
and torus variables on each discrete fibre and has finite bounds for all four multi-indices. -/
def elementarySchwartzSubmodule (m n r : ℕ) (F : Type*) :
    Submodule ℂ (ElementaryLCAModel m n r F → ℂ) where
  carrier := {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
    ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)}
  zero_mem' := elementarySchwartzSubmodule_zero_mem
  add_mem' := elementarySchwartzSubmodule_add_mem
  smul_mem' := elementarySchwartzSubmodule_smul_mem

end


section

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Paper: Definition D.1.3.1, p. 750. Every weighted bound vanishes on the zero function. -/
theorem elementarySchwartzSeminorm_map_zero (i : ElementarySchwartzIndex m n r) :
    (elementarySchwartzBound (0 : elementarySchwartzSubmodule m n r F).val i).toReal = 0 := by
  change (elementarySchwartzBound (0 : ElementaryLCAModel m n r F → ℂ) i).toReal = 0
  simp [elementarySchwartzBound, elementaryPartial]

/-- Paper: Definition D.1.3.1, p. 750. Each real-valued weighted bound is subadditive
on the Schwartz submodule. -/
theorem elementarySchwartzSeminorm_add_le (i : ElementarySchwartzIndex m n r)
    (f g : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (f + g).val i).toReal ≤
      (elementarySchwartzBound f.val i).toReal + (elementarySchwartzBound g.val i).toReal := by
  change (elementarySchwartzBound (f.val + g.val) i).toReal ≤ _
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(f.property.2 i).ne, (g.property.2 i).ne⟩)
    (elementarySchwartzBound_add_le f.property.1 g.property.1 i)).trans_eq
    (ENNReal.toReal_add (f.property.2 i).ne (g.property.2 i).ne)

/-- Paper: Definition D.1.3.1, p. 750. Scaling a Schwartz function multiplies its
real-valued weighted bound by the norm of the scalar. -/
theorem elementarySchwartzSeminorm_smul (i : ElementarySchwartzIndex m n r)
    (c : ℂ) (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (c • f).val i).toReal =
      ‖c‖ * (elementarySchwartzBound f.val i).toReal := by
  change (elementarySchwartzBound (c • f.val) i).toReal = _
  rw [elementarySchwartzBound_smul c f.property.1, ENNReal.toReal_mul]
  rfl

/-- Paper: Definition D.1.3.1, p. 750. Each real-valued weighted bound is invariant
under negation on the Schwartz submodule. -/
theorem elementarySchwartzSeminorm_neg (i : ElementarySchwartzIndex m n r)
    (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (-f).val i).toReal =
      (elementarySchwartzBound f.val i).toReal := by
  change (elementarySchwartzBound (-f.val) i).toReal = _
  rw [← neg_one_smul ℂ f.val, elementarySchwartzBound_smul (-1 : ℂ) f.property.1]
  simp

/-- Paper: Definition D.1.3.1, p. 750. On the Schwartz submodule each finite
weighted bound gives a real-valued seminorm. -/
def elementarySchwartzSeminorm (i : ElementarySchwartzIndex m n r) :
    Seminorm ℂ (elementarySchwartzSubmodule m n r F) where
  toFun f := (elementarySchwartzBound f.val i).toReal
  map_zero' := elementarySchwartzSeminorm_map_zero i
  add_le' := elementarySchwartzSeminorm_add_le i
  smul' := elementarySchwartzSeminorm_smul i
  neg' := elementarySchwartzSeminorm_neg i

end

/-- Paper: Definition D.1.3.1, p. 750. The locally convex topology on
the Schwartz space is generated by the weighted derivative seminorms. -/
abbrev ElementarySchwartz (m n r : ℕ) (F : Type*) :=
  WithGeneratingSeminorms (elementarySchwartzSubmodule m n r F) elementarySchwartzSeminorm

instance : CoeFun (ElementarySchwartz m n r F) (fun _ ↦ ElementaryLCAModel m n r F → ℂ) where
  coe f := (show elementarySchwartzSubmodule m n r F from f).val

/-- Paper: Definition D.1.3.1, p. 750. At zero multi-indices the seminorm is the
uniform norm of the underlying function. -/
theorem elementarySchwartzSeminorm_zero (f : ElementarySchwartz m n r F) :
    elementarySchwartzSeminorm (0, 0, 0, 0) f = ⨆ g, ‖f g‖ := by
  change (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal = _
  rw [elementarySchwartzBound_zero, ENNReal.toReal_iSup (fun _ ↦ ENNReal.coe_ne_top)]
  rfl

/-- Paper: Definition D.1.3.1, p. 750. The canonical seminorm family generates
the topology of the space. -/
theorem elementarySchwartz_withSeminorms :
    WithSeminorms (E := ElementarySchwartz m n r F) elementarySchwartzSeminorm := by
  exact withGeneratingSeminorms_spec _ _

/-- Paper: Remark D.1.3.2, p. 750. The Schwartz topology is Hausdorff. -/
theorem elementarySchwartz_t2 : T2Space (ElementarySchwartz m n r F) := by
  let hp := withGeneratingSeminorms_spec (elementarySchwartzSubmodule m n r F) elementarySchwartzSeminorm
  have : T1Space (ElementarySchwartz m n r F) := hp.T1_of_separating fun f hf ↦ by
    let i : ElementarySchwartzIndex m n r := (0, 0, 0, 0)
    refine ⟨i, fun hzero ↦ hf ?_⟩
    apply Subtype.ext
    funext g
    have h : ‖f g‖ ≤ elementarySchwartzSeminorm i f := by
      change (‖f.val g‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
      apply ENNReal.toReal_mono (f.property.2 i).ne
      rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
      exact le_iSup (fun x ↦ (‖f.val x‖₊ : ENNReal)) g
    change f.val g = 0
    exact norm_eq_zero.mp (le_antisymm (h.trans_eq hzero) (norm_nonneg _))
  infer_instance

/-- A continuous homomorphism of elementary groups lifts on each discrete fibre to an affine map with
the same real-linear part on every fibre. -/
theorem elementaryCover_hom_affine
    {m' n' r' : ℕ} {F' : Type*} [AddCommGroup F'] [TopologicalSpace F']
    [DiscreteTopology F'] [Finite F']
    (φ : ElementaryLCAModel m n r F →+ ElementaryLCAModel m' n' r' F') (hφ : Continuous φ) :
    let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    let Y := EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')
    ∃ L : X →L[ℝ] Y, ∀ (a : Fin r → ℤ) (b : F),
      ∃ (y : Y) (a' : Fin r' → ℤ) (b' : F'), ∀ xt : X,
        φ (elementaryCover xt a b) = elementaryCover (L xt + y) a' b' := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')
  let G := ElementaryLCAModel m n r F
  let G' := ElementaryLCAModel m' n' r' F'
  let q : X →+ G := elementaryCoverHom
  have hq : Continuous q := elementaryCoverHom_continuous
  let a₀ := φ.comp q
  have ha₀ : Continuous a₀ := hφ.comp hq
  let aR := (AddMonoidHom.fst _ _).comp a₀
  let aT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp a₀)
  choose l hl hlift using fun i : Fin n' ↦ exists_addCircle_addMonoidHom_lift
    ((Pi.evalAddMonoidHom _ i).comp aT) ((continuous_apply i).comp ha₀.snd.fst)
  let A : X →+ Y := aR.prod ((EuclideanSpace.equiv (Fin n') ℝ).symm.toLinearMap.toAddMonoidHom.comp
    (AddMonoidHom.pi l))
  have hA : Continuous A :=
    ha₀.fst.prodMk ((PiLp.continuous_toLp 2 _).comp (continuous_pi hl))
  have hDiscrete (x : X) : (a₀ x).2.2 = 0 := by
    have h := TotallyDisconnectedSpace.eq_of_continuous _ ha₀.snd.snd x 0
    rw [map_zero a₀] at h
    exact h
  refine ⟨A.toRealLinearMap hA, fun a b ↦ ?_⟩
  let c := φ (elementaryCover (0 : X) a b)
  obtain ⟨u, hu⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  refine ⟨(c.1, u), c.2.2.1, c.2.2.2, fun x ↦ ?_⟩
  have hShift : q x + elementaryCover 0 a b = elementaryCover x a b := by
    rw [add_comm]
    simpa only [zero_add] using (elementaryCover_add (0 : X) x a b).symm
  rw [← hShift, map_add]
  change a₀ x + c = elementaryCover (A x + (c.1, u)) c.2.2.1 c.2.2.2
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i
    have hui := congrArg (fun y : G' ↦ y.2.1 i) hu
    change (a₀ x).2.1 i + c.2.1 i = ((l i x + u i : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add, hlift i x]
    exact congrArg ((a₀ x).2.1 i + ·) hui.symm
  · change (a₀ x).2.2 + c.2.2 = c.2.2
    rw [hDiscrete, zero_add]

private theorem elementaryCover_pullback_affine
    (φ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F) :
    let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    ∃ L : X →L[ℝ] X, ∀ (a : Fin r → ℤ) (b : F),
      ∃ (y : X) (a' : Fin r → ℤ) (b' : F), ∀ xt : X,
        φ (elementaryCover xt a b) = elementaryCover (L xt + y) a' b' :=
  elementaryCover_hom_affine φ.toAddEquiv.toAddMonoidHom φ.continuous

/-- Elementary fibre regularity pulls back along any continuous group homomorphism. -/
theorem elementaryContDiff_hom
    {m' n' r' : ℕ} {F' : Type*} [AddCommGroup F'] [TopologicalSpace F']
    [DiscreteTopology F'] [Finite F'] {s : WithTop ℕ∞}
    (φ : ElementaryLCAModel m n r F →+ ElementaryLCAModel m' n' r' F') (hφ : Continuous φ)
    (f : ElementaryLCAModel m' n' r' F' → ℂ)
    (hf : ∀ a b, ContDiff ℝ s (fun x ↦ f (elementaryCover x a b))) :
    ∀ a b, ContDiff ℝ s (fun x ↦ f (φ (elementaryCover x a b))) := by
  obtain ⟨L, hL⟩ := elementaryCover_hom_affine φ hφ
  intro a b
  obtain ⟨y, a', b', hy⟩ := hL a b
  have he : (fun x ↦ f (φ (elementaryCover x a b))) =
      fun x ↦ f (elementaryCover (L x + y) a' b') := funext fun x ↦ congrArg f (hy x)
  rw [he]
  exact (hf a' b').comp (L.contDiff.add contDiff_const)

/-- Paper: (D.1.3.7), p. 750. The monomial weight in the real and integer coordinates. -/
private def elementarySchwartzMonomial (α : Fin m → ℕ) (δ : Fin r → ℕ)
    (x : EuclideanSpace ℝ (Fin m)) (a : Fin r → ℤ) : ℂ :=
  (∏ k, (x k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)

omit [DiscreteTopology F] in
/-- A weighted coordinate monomial composed with an elementary group automorphism
is a finite linear combination of coordinate monomials on the same group.
The projection onto the real and lattice factors kills the compact torus and finite
factors, and additivity gives linear coordinate forms on the remaining two factors. -/
private theorem elementarySchwartz_monomial_comp
    (φ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F)
    (α : Fin m → ℕ) (δ : Fin r → ℕ) :
    ∃ (s : Finset ((Fin m → ℕ) × (Fin r → ℕ)))
      (c : ((Fin m → ℕ) × (Fin r → ℕ)) → ℂ), ∀ g,
        elementarySchwartzMonomial α δ (φ g).1 (φ g).2.2.1 =
          ∑ p ∈ s, c p * elementarySchwartzMonomial p.1 p.2 g.1 g.2.2.1 := by
  classical
  let V := EuclideanSpace ℝ (Fin m)
  let Z := Fin r → ℤ
  let K := (Fin n → AddCircle (1 : ℝ)) × F
  let G := ElementaryLCAModel m n r F
  let J := Fin m ⊕ Fin r
  let eR : V →+ G :=
    ⟨⟨fun x ↦ (x, 0, 0, 0), rfl⟩, fun _ _ ↦
      Prod.ext rfl (Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (zero_add _).symm))⟩
  let eZ : Z →+ G :=
    ⟨⟨fun a ↦ (0, 0, a, 0), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (Prod.ext rfl (zero_add _).symm))⟩
  let eK : K →+ G :=
    ⟨⟨fun z ↦ (0, z.1, 0, z.2), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl))⟩
  let e (j : J) : G := Sum.elim
    (fun i ↦ eR (EuclideanSpace.single i 1)) (fun i ↦ eZ (Pi.single i 1)) j
  let coord (j : J) : G →+ ℝ := Sum.elim
    (fun i : Fin m ↦
      ⟨⟨fun g : G ↦ g.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r ↦
      (Int.castAddHom ℝ).comp ⟨⟨fun g : G ↦ g.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hcoord (j : J) : Continuous (coord j) := by
    cases j with
    | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
    | inr i =>
      exact (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ℝ))).comp
        ((continuous_apply i).comp continuous_snd.snd.fst)
  have hlinear (h : G →+ ℝ) (hh : Continuous h) (g : G) :
      h g = ∑ j, coord j g * h (e j) := by
    let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
    let hK := h.comp eK
    have hKcont : Continuous hK :=
      hh.comp (continuous_const.prodMk (continuous_fst.prodMk
        (continuous_const.prodMk continuous_snd)))
    have hvanish (z : K) : hK z = 0 := by
      obtain ⟨M, hM⟩ := (isCompact_range hKcont.norm).bddAbove
      by_contra hz
      obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖hK z‖)
      have hle := hM (Set.mem_range_self (N • z))
      change ‖hK (N • z)‖ ≤ M at hle
      rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hle
      exact (not_lt_of_ge hle) ((div_lt_iff₀ (norm_pos_iff.mpr hz)).mp hN)
    let hR := (h.comp eR).toRealLinearMap (hh.comp (continuous_id.prodMk continuous_const))
    let basisR := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    let basisZ := Pi.basisFun ℤ (Fin r)
    have hr (x : V) : h (eR x) = ∑ i, x i * h (eR (EuclideanSpace.single i 1)) := by
      have he := congrArg hR (basisR.sum_repr x)
      simpa [hR, basisR, smul_eq_mul] using he.symm
    have hz (a : Z) : h (eZ a) = ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1)) := by
      have he := congrArg (h.comp eZ) (basisZ.sum_repr a)
      rw [map_sum] at he
      simp_rw [map_zsmul, zsmul_eq_mul] at he
      simpa [basisZ] using he.symm
    rcases g with ⟨x, z, a, b⟩
    have hdecomp : (x, z, a, b) = eR x + eZ a + eK (z, b) := by
      change (x, z, a, b) = ((x + 0) + 0, (0 + 0) + z, (0 + a) + 0, (0 + 0) + b)
      simp
    have hKzero : h (eK (z, b)) = 0 := hvanish (z, b)
    rw [Fintype.sum_sum_type]
    change h (x, z, a, b) =
      (∑ i, x i * h (eR (EuclideanSpace.single i 1))) +
        ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1))
    rw [hdecomp, map_add, map_add, hKzero, add_zero, hr, hz]
  let v (g : G) (j : J) : ℂ := Complex.ofRealHom (coord j g)
  have hvR (g : G) (i : Fin m) : v g (.inl i) = (g.1 i : ℂ) := rfl
  have hvZ (g : G) (i : Fin r) : v g (.inr i) = (g.2.2.1 i : ℂ) :=
    Complex.ofReal_intCast _
  let P (j : J) : MvPolynomial J ℂ :=
    ∑ k : J, MvPolynomial.C (v (φ (e k)) j) * MvPolynomial.X k
  have hP (g : G) (j : J) : MvPolynomial.eval (v g) (P j) = v (φ g) j := by
    have he : coord j (φ g) = ∑ k, coord k g * coord j (φ (e k)) :=
      hlinear ((coord j).comp φ.toAddEquiv.toAddMonoidHom)
        ((hcoord j).comp φ.continuous) g
    calc
      MvPolynomial.eval (v g) (P j) = ∑ k, v g k * v (φ (e k)) j := by
        simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
        exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
      _ = v (φ g) j := by
        simpa only [v, map_sum, map_mul] using congrArg Complex.ofRealHom he.symm
  let Q := (∏ i, P (.inl i) ^ α i) * (∏ i, P (.inr i) ^ δ i)
  have hQ (g : G) :
      MvPolynomial.eval (v g) Q = elementarySchwartzMonomial α δ (φ g).1 (φ g).2.2.1 := by
    simp only [Q, map_mul, map_prod, map_pow, hP, hvR, hvZ, elementarySchwartzMonomial]
  let orders : (J →₀ ℕ) ≃ ((Fin m → ℕ) × (Fin r → ℕ)) :=
    Finsupp.equivFunOnFinite.trans (Equiv.sumArrowEquivProdArrow _ _ _)
  refine ⟨Q.support.map orders.toEmbedding, fun p ↦ Q.coeff (orders.symm p), fun g ↦ ?_⟩
  rw [← hQ, MvPolynomial.eval_eq', Finset.sum_map]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Fintype.prod_sum_type]
  have hOrdersR (i : Fin m) : (orders d).1 i = d (.inl i) := rfl
  have hOrdersZ (i : Fin r) : (orders d).2 i = d (.inr i) := rfl
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply, hvR, hvZ,
    elementarySchwartzMonomial, hOrdersR, hOrdersZ]

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
/-- The standard real and lifted torus coordinate directions on a smooth fibre. -/
abbrev elementaryFibreBasis (m n : ℕ) :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

def elementaryDirectionList (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    List (Fin m ⊕ Fin n) :=
  (List.ofFn fun i ↦ List.replicate (β i) (Sum.inl i)).flatten ++
    (List.ofFn fun i ↦ List.replicate (γ i) (Sum.inr i)).flatten

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
theorem elementaryPartial_eq_basis
    (f : ElementaryLCAModel m n r F → ℂ) (a : Fin r → ℤ) (b : F)
    (d : Fin m → ℕ) (e : Fin n → ℕ)
    (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    elementaryPartial f d e x a b =
      iteratedFDeriv ℝ (elementaryDirectionList d e).length (fun z ↦ f (elementaryCover z a b)) x
        (fun i ↦ elementaryFibreBasis m n ((elementaryDirectionList d e).get i)) := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := Fin m ⊕ Fin n
  let B := elementaryFibreBasis m n
  let dirs := elementaryDirectionList (m := m) (n := n)
  have hdirs (b : Fin m → ℕ) (g : Fin n → ℕ) :
      (dirs b g).map B =
        (List.ofFn fun i ↦ List.replicate (b i) (EuclideanSpace.single i 1, 0)).flatten ++
        (List.ofFn fun i ↦ List.replicate (g i) (0, EuclideanSpace.single i 1)).flatten := by
    have hInl (i : Fin m) : B (.inl i) = (EuclideanSpace.single i 1, 0) := by
      dsimp only [B, elementaryFibreBasis]
      rw [Module.Basis.prod_apply]
      simp only [Sum.elim_inl, Function.comp_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply, LinearMap.inl_apply]
    have hInr (i : Fin n) : B (.inr i) = (0, EuclideanSpace.single i 1) := by
      dsimp only [B, elementaryFibreBasis]
      rw [Module.Basis.prod_apply]
      simp only [Sum.elim_inr, Function.comp_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply, LinearMap.inr_apply]
    simp only [dirs, elementaryDirectionList, List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def,
      List.map_replicate, hInl, hInr]

  dsimp only [elementaryPartial]
  rw [← hdirs d e]
  have hlength (k : ℕ) (hk : k = (dirs d e).length) :
      iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x
        (fun i ↦ B ((dirs d e).get (Fin.cast hk i))) =
        iteratedFDeriv ℝ (dirs d e).length (fun z ↦ f (elementaryCover z a b)) x
          (fun i ↦ B ((dirs d e).get i)) := by
    subst k
    rfl
  have hlen : ((dirs d e).map B).length = (dirs d e).length := List.length_map B
  have hget : ((dirs d e).map B).get =
      fun i ↦ B ((dirs d e).get (Fin.cast hlen i)) := by
    funext i
    simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  rw [hget]
  exact hlength _ hlen

/-- Any iterated derivative on coordinate vectors is the mixed partial with
those direction multiplicities. -/
theorem elementaryIteratedFDeriv_basis {k : ℕ} (t : Fin k → Fin m ⊕ Fin n) :
    ∃ (β : Fin m → ℕ) (γ : Fin n → ℕ),
      ∀ (f : ElementaryLCAModel m n r F → ℂ) (a : Fin r → ℤ) (b : F),
        ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x a b)) →
        ∀ x, iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x
          (fun i ↦ elementaryFibreBasis m n (t i)) = elementaryPartial f β γ x a b := by
  classical
  let J := Fin m ⊕ Fin n
  letI : DecidableEq J := Classical.decEq J
  letI : BEq J := ⟨fun a b ↦ decide (a = b)⟩
  letI : LawfulBEq J :=
    { eq_of_beq := of_decide_eq_true
      rfl := of_decide_eq_self_eq_true _ }
  let dirs := elementaryDirectionList (m := m) (n := n)
  let indices (t : Fin k → J) : (Fin m → ℕ) × (Fin n → ℕ) :=
    (fun i ↦ (List.ofFn t).count (.inl i), fun j ↦ (List.ofFn t).count (.inr j))
  have hPerm : (List.ofFn t).Perm (dirs (indices t).1 (indices t).2) := by
    apply List.perm_iff_count.mpr
    intro j
    cases j <;>
      simp [dirs, elementaryDirectionList, indices, List.count_flatten, List.map_ofFn,
        List.count_replicate, beq_iff_eq, List.sum_ofFn]
  refine ⟨(indices t).1, (indices t).2, fun f a b hf x ↦ ?_⟩
  rw [elementaryPartial_eq_basis]
  have hlength (n' : ℕ) (hn : n' = k) :
      iteratedFDeriv ℝ n' (fun z ↦ f (elementaryCover z a b)) x
        (fun i ↦ elementaryFibreBasis m n (t (Fin.cast hn i))) =
      iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x
        (fun i ↦ elementaryFibreBasis m n (t i)) := by
    subst n'
    rfl
  rw [← hlength _ List.length_ofFn]
  simpa only [List.get_ofFn] using
    iteratedFDeriv_apply_list_perm hf (elementaryFibreBasis m n) hPerm x

/-- The chain rule on a lifted fibre expresses each mixed partial after an affine
change of variables as a finite linear combination of mixed partials before the
change. Its coefficients depend only on the linear part and the derivative orders. -/
private theorem elementaryPartial_comp_affine
    (L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    ∃ (s : Finset ((Fin m → ℕ) × (Fin n → ℕ)))
      (c : ((Fin m → ℕ) × (Fin n → ℕ)) → ℝ),
      ∀ (f h : ElementaryLCAModel m n r F → ℂ) y a b a' b',
        ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x a' b')) →
        (∀ x, h (elementaryCover x a b) = f (elementaryCover (L x + y) a' b')) →
        ∀ x, elementaryPartial h β γ x a b =
          ∑ p ∈ s, c p • elementaryPartial f p.1 p.2 (L x + y) a' b' := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := Fin m ⊕ Fin n
  letI : DecidableEq J := Classical.decEq J
  letI : BEq J := ⟨fun a b ↦ decide (a = b)⟩
  letI : LawfulBEq J :=
    { eq_of_beq := of_decide_eq_true
      rfl := of_decide_eq_self_eq_true _ }
  let B := elementaryFibreBasis m n
  let dirs := elementaryDirectionList (m := m) (n := n)
  let l := dirs β γ
  let T := Fin l.length → J
  let indices (t : T) : (Fin m → ℕ) × (Fin n → ℕ) :=
    (fun i ↦ (List.ofFn t).count (.inl i), fun j ↦ (List.ofFn t).count (.inr j))
  let coeff (t : T) := ∏ i, B.repr (L (B (l.get i))) (t i)
  let s := Finset.univ.image indices
  refine ⟨s, fun p ↦ ∑ t ∈ Finset.univ.filter (fun t ↦ indices t = p), coeff t, ?_⟩
  intro f h y a b a' b' hf hEq x
  let f₀ : X → ℂ := fun z ↦ f (elementaryCover z a' b')
  let D := iteratedFDeriv ℝ l.length f₀ (L x + y)
  have hPerm (t : T) : (List.ofFn t).Perm (dirs (indices t).1 (indices t).2) := by
    apply List.perm_iff_count.mpr
    intro j
    cases j with
    | inl i =>
      simp [dirs, elementaryDirectionList, indices, List.count_flatten, List.map_ofFn, List.count_replicate, beq_iff_eq, List.sum_ofFn]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        exact ite_eq_right (fun h ↦ hj (Sum.inl.inj h))
      · simp
    | inr i =>
      simp [dirs, elementaryDirectionList, indices, List.count_flatten, List.map_ofFn, List.count_replicate, beq_iff_eq, List.sum_ofFn]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        exact ite_eq_right (fun h ↦ hj (Sum.inr.inj h))
      · simp
  have hterm (t : T) : D (fun i ↦ B (t i)) =
      elementaryPartial f (indices t).1 (indices t).2 (L x + y) a' b' := by
    rw [elementaryPartial_eq_basis]
    have hlength (k : ℕ) (hk : k = l.length) :
        iteratedFDeriv ℝ k f₀ (L x + y) (fun i ↦ B (t (Fin.cast hk i))) =
          D (fun i ↦ B (t i)) := by
      subst k
      rfl
    rw [← hlength _ List.length_ofFn]
    simpa only [f₀, List.get_ofFn] using
      iteratedFDeriv_apply_list_perm hf B (hPerm t) (L x + y)
  have hchain :
      elementaryPartial h β γ x a b = D (fun i ↦ L (B (l.get i))) := by
    rw [elementaryPartial_eq_basis, show (fun z ↦ h (elementaryCover z a b)) =
      (fun z ↦ f₀ (z + y)) ∘ L from funext hEq,
      L.iteratedFDeriv_comp_right
        (show ContDiff ℝ ∞ (fun z : X ↦ f₀ (z + y)) from hf.comp
          (contDiff_id.add contDiff_const)) x (finiteOrder_le_smoothOrder _),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  rw [hchain]
  let v (i : Fin l.length) := L (B (l.get i))
  change D.toMultilinearMap v = _
  conv_lhs => rw [show v = (fun i ↦ ∑ j, B.repr (v i) j • B j) from
    funext fun i ↦ (B.sum_repr (v i)).symm]
  rw [D.toMultilinearMap.map_sum]
  simp_rw [D.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe,
    hterm, Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (t := s)
    (fun t _ ↦ Finset.mem_image_of_mem indices (Finset.mem_univ t))]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun t ht ↦ ?_
  rw [(Finset.mem_filter.mp ht).2]

/-- Each weighted bound of the pullback is controlled by a continuous seminorm
of the original Schwartz function. -/
private theorem elementarySchwartzBound_pullback_le
    (φ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F)
    (i : ElementarySchwartzIndex m n r) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧
      ∀ f : ElementarySchwartz m n r F,
        elementarySchwartzBound (fun g ↦ f (φ g)) i ≤ ENNReal.ofReal (q f) := by
  obtain ⟨L, hL⟩ := elementaryCover_pullback_affine φ
  obtain ⟨s, c, hw⟩ := elementarySchwartz_monomial_comp φ.symm i.1 i.2.2.2
  obtain ⟨t, d, hd⟩ := elementaryPartial_comp_affine (r := r) (F := F) L i.2.1 i.2.2.1
  let p (u : (Fin m → ℕ) × (Fin r → ℕ)) (v : (Fin m → ℕ) × (Fin n → ℕ)) :
      Seminorm ℂ (ElementarySchwartz m n r F) :=
    (‖c u * (d v : ℂ)‖₊ : ℝ≥0) • elementarySchwartzSeminorm (u.1, v.1, v.2, u.2)
  let q : Seminorm ℂ (ElementarySchwartz m n r F) := ∑ u ∈ s, ∑ v ∈ t, p u v
  have hq : ∀ f : ElementarySchwartz m n r F, q f = ∑ u ∈ s, ∑ v ∈ t, p u v f := by
    intro f
    change FunLike.coeAddMonoidHom _ _ _ (∑ u ∈ s, ∑ v ∈ t, p u v) f = _
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    change FunLike.coeAddMonoidHom _ _ _ (∑ v ∈ t, p u v) f = _
    simp [map_sum, Finset.sum_apply]
  refine ⟨q, ?_, fun f ↦ ?_⟩
  · exact Seminorm.continuous_finsetSum fun u _ ↦ Seminorm.continuous_finsetSum fun v _ ↦ by
      change Continuous fun f : ElementarySchwartz m n r F ↦
        ‖c u * (d v : ℂ)‖ * elementarySchwartzSeminorm (u.1, v.1, v.2, u.2) f
      exact continuous_const.mul (elementarySchwartz_withSeminorms.continuous_seminorm _)
  · refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    obtain ⟨y, a', b', hφ⟩ := hL a b
    have hw' := hw (φ (elementaryCover x a b))
    rw [φ.symm_apply_apply, hφ x] at hw'
    change elementarySchwartzMonomial i.1 i.2.2.2 x.1 a =
      ∑ u ∈ s, c u * elementarySchwartzMonomial u.1 u.2 (L x + y).1 a' at hw'
    have hd' := hd f (fun g ↦ f (φ g)) y a b a' b' (f.property.1 a' b')
      (fun z ↦ congrArg (fun g ↦ f g) (hφ z)) x
    change (‖elementarySchwartzMonomial i.1 i.2.2.2 x.1 a *
      elementaryPartial (fun g ↦ f (φ g)) i.2.1 i.2.2.1 x a b‖₊ : ℝ≥0∞) ≤ _
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [coe_nnnorm, hw', hd', Finset.sum_mul, hq]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ ↦ ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
    rw [Complex.real_smul]
    rw [show c u * elementarySchwartzMonomial u.1 u.2 (L x + y).1 a' *
        ((d v : ℂ) * elementaryPartial f.val v.1 v.2 (L x + y) a' b') =
        (c u * (d v : ℂ)) * (elementarySchwartzMonomial u.1 u.2 (L x + y).1 a' *
          elementaryPartial f.val v.1 v.2 (L x + y) a' b') by ring]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    let j : ElementarySchwartzIndex m n r := (u.1, v.1, v.2, u.2)
    change (‖elementarySchwartzMonomial u.1 u.2 (L x + y).1 a' *
      elementaryPartial f.val v.1 v.2 (L x + y) a' b'‖₊ : ℝ≥0∞).toReal ≤
      (elementarySchwartzBound f.val j).toReal
    exact ENNReal.toReal_mono (f.property.2 j).ne
      (le_iSup_of_le (L x + y) (le_iSup_of_le a' (le_iSup_of_le b' le_rfl)))

/-- Paper: Lemma D.1.3.3, p. 750. Pullback by a topological group automorphism
gives a linear topological automorphism of the elementary Schwartz space. -/
theorem elementarySchwartz_pullback (φ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F) :
    ∃ e : ElementarySchwartz m n r F ≃L[ℂ] ElementarySchwartz m n r F,
      ∀ f g, e f g = f (φ g) := by
  have hmem (ψ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F)
      (f : ElementarySchwartz m n r F) :
      (fun g ↦ f (ψ g)) ∈ elementarySchwartzSubmodule m n r F := by
    obtain ⟨L, hL⟩ := elementaryCover_pullback_affine ψ
    refine ⟨fun a b ↦ ?_, fun i ↦ ?_⟩
    · obtain ⟨y, a', b', hψ⟩ := hL a b
      simp_rw [hψ]
      exact (f.property.1 a' b').comp (L.contDiff.add contDiff_const)
    · obtain ⟨q, _, hq⟩ := elementarySchwartzBound_pullback_le ψ i
      exact (hq f).trans_lt ENNReal.ofReal_lt_top
  let pull (ψ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F) :
      ElementarySchwartz m n r F →ₗ[ℂ] ElementarySchwartz m n r F :=
    { toFun := fun f ↦ ⟨fun g ↦ f (ψ g), hmem ψ f⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hcont (ψ : ElementaryLCAModel m n r F ≃ₜ+ ElementaryLCAModel m n r F) :
      Continuous (pull ψ) := by
    apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
    intro i
    obtain ⟨q, hq, hq'⟩ := elementarySchwartzBound_pullback_le ψ i
    refine Seminorm.continuous_of_le hq (fun f ↦ ?_)
    change (elementarySchwartzBound (fun g ↦ f (ψ g)) i).toReal ≤ q f
    simpa only [ENNReal.toReal_ofReal (apply_nonneg q f)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hq' f)
  exact ⟨ContinuousLinearEquiv.equivOfInverse ⟨pull φ, hcont φ⟩ ⟨pull φ.symm, hcont φ.symm⟩
    (fun f ↦ Subtype.ext (funext fun g ↦ congrArg (fun x ↦ f x) (φ.apply_symm_apply g)))
    (fun f ↦ Subtype.ext (funext fun g ↦ congrArg (fun x ↦ f x) (φ.symm_apply_apply g))),
    fun _ _ ↦ rfl⟩

/-- `1 + ‖x‖ ^ j` is controlled by the constant term and the pure powers of the coordinates. -/
lemma one_add_euclidean_pow_le {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (j : ℕ) :
    1 + ‖x‖ ^ j ≤
      (1 + (Real.sqrt (d : ℝ)) ^ j) * (1 + ∑ i : Fin d, |x i| ^ j) := by
  cases j with
  | zero =>
    simp only [pow_zero]
    have hsum : (0 : ℝ) ≤ ∑ i : Fin d, (1 : ℝ) :=
      Finset.sum_nonneg fun _ _ => zero_le_one
    linarith
  | succ j =>
    cases d with
    | zero =>
      have : IsEmpty (Fin 0) := ⟨Fin.elim0⟩
      have hx0 : ‖x‖ = 0 := by
        rw [← sq_eq_zero_iff, EuclideanSpace.real_norm_sq_eq]
        simp [Finset.univ_eq_empty]
      simp [hx0, Real.sqrt_zero, zero_pow (Nat.succ_ne_zero _), Finset.univ_eq_empty]
    | succ d =>
      have : Nonempty (Fin (Nat.succ d)) := ⟨0⟩
      obtain ⟨i0, hi0, hmax⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Fin (Nat.succ d)))
          (fun i => |x i|) Finset.univ_nonempty
      have hsq : ‖x‖ ^ 2 ≤ (Nat.succ d : ℝ) * |x i0| ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc
          ∑ i, (x i) ^ 2 = ∑ i, |x i| ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← sq_abs]
          _ ≤ ∑ i, |x i0| ^ 2 :=
            Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (abs_nonneg _) (hmax i hi) 2
          _ = (Nat.succ d : ℝ) * |x i0| ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hnorm : ‖x‖ ≤ Real.sqrt (Nat.succ d : ℝ) * |x i0| := by
        refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        exact hsq
      set t : ℝ := (Real.sqrt (Nat.succ d : ℝ)) ^ Nat.succ j
      have ht : 0 ≤ t := pow_nonneg (Real.sqrt_nonneg _) _
      have hpow : ‖x‖ ^ Nat.succ j ≤ t * |x i0| ^ Nat.succ j := by
        calc
          ‖x‖ ^ Nat.succ j ≤ (Real.sqrt (Nat.succ d : ℝ) * |x i0|) ^ Nat.succ j :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm _
          _ = t * |x i0| ^ Nat.succ j := by rw [mul_pow]
      have hi0le : |x i0| ^ Nat.succ j ≤ ∑ i, |x i| ^ Nat.succ j :=
        Finset.single_le_sum (fun i _ => pow_nonneg (abs_nonneg (x i)) (Nat.succ j)) hi0
      have hnormsum : ‖x‖ ^ Nat.succ j ≤ t * ∑ i, |x i| ^ Nat.succ j :=
        hpow.trans (mul_le_mul_of_nonneg_left hi0le ht)
      have hS : 0 ≤ ∑ i : Fin (Nat.succ d), |x i| ^ Nat.succ j :=
        Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _
      calc
        1 + ‖x‖ ^ Nat.succ j ≤ 1 + t * ∑ i, |x i| ^ Nat.succ j :=
          add_le_add_right hnormsum 1
        _ ≤ (1 + t) * (1 + ∑ i, |x i| ^ Nat.succ j) := by nlinarith

/-- A monomial in the coordinates is at most the corresponding power of the Euclidean norm. -/
lemma prod_abs_pow_le_norm_pow {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (α : Fin d → ℕ) :
    ∏ k, |x k| ^ α k ≤ ‖x‖ ^ ∑ k, α k := by
  calc
    ∏ k, |x k| ^ α k ≤ ∏ k, ‖x‖ ^ α k := by
      refine Finset.prod_le_prod (fun _ _ => pow_nonneg (abs_nonneg _) _) fun k _ => ?_
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x k) (α k)
    _ = ‖x‖ ^ ∑ k, α k := Finset.prod_pow_eq_pow_sum _ _ _

/-- Mixed partials are additive on fibrewise smooth functions. -/
lemma elementaryPartial_add {f g : ElementaryLCAModel m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (hg : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b)))
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (f + g) β γ xt a b =
      elementaryPartial f β γ xt a b + elementaryPartial g β γ xt a b := by
  have hadd (n : ℕ) :
      iteratedFDeriv ℝ n (fun v ↦ (f + g) (elementaryCover v a b)) xt =
        iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt +
        iteratedFDeriv ℝ n (fun v ↦ g (elementaryCover v a b)) xt :=
    iteratedFDeriv_add_apply ((hf a b).of_le (finiteOrder_le_smoothOrder n)).contDiffAt
      ((hg a b).of_le (finiteOrder_le_smoothOrder n)).contDiffAt
  dsimp only [elementaryPartial]
  rw [hadd]
  rfl

/-- Mixed partials are homogeneous on fibrewise smooth functions. -/
lemma elementaryPartial_smul (c : ℂ) {f : ElementaryLCAModel m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (c • f) β γ xt a b = c • elementaryPartial f β γ xt a b := by
  have hsmul (n : ℕ) :
      iteratedFDeriv ℝ n (fun v ↦ (c • f) (elementaryCover v a b)) xt =
        c • iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt :=
    iteratedFDeriv_const_smul_apply ((hf a b).of_le (finiteOrder_le_smoothOrder n)).contDiffAt
  dsimp only [elementaryPartial]
  rw [hsmul]
  rfl

/-- A coordinate monomial times a partial is bounded by the corresponding Euclidean weight. -/
lemma monomial_norm_le_p1 (f : ElementaryLCAModel m n r F → ℂ)
    (α : Fin m → ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ) (δ : Fin r → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖((∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)) *
        elementaryPartial f β γ xt a b‖ ≤
      (1 + ‖xt.1‖ ^ ∑ k, α k) *
        (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ ∑ k, δ k) *
        ‖elementaryPartial f β γ xt a b‖ := by
  let aVec : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun k ↦ (a k : ℝ))
  have hX : ‖∏ k, (xt.1 k : ℂ) ^ α k‖ = ∏ k, |xt.1 k| ^ α k := by
    simp [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hA : ‖∏ k, (a k : ℂ) ^ δ k‖ = ∏ k, |aVec k| ^ δ k := by
    simp [aVec, norm_prod, norm_pow, Complex.norm_intCast]
  rw [norm_mul, norm_mul, hX, hA]
  have hx : ∏ k, |xt.1 k| ^ α k ≤ 1 + ‖xt.1‖ ^ ∑ k, α k :=
    (prod_abs_pow_le_norm_pow xt.1 α).trans (le_add_of_nonneg_left zero_le_one)
  have ha : ∏ k, |aVec k| ^ δ k ≤ 1 + ‖aVec‖ ^ ∑ k, δ k :=
    (prod_abs_pow_le_norm_pow aVec δ).trans (le_add_of_nonneg_left zero_le_one)
  have hprod :
      (∏ k, |xt.1 k| ^ α k) * (∏ k, |aVec k| ^ δ k) ≤
        (1 + ‖xt.1‖ ^ ∑ k, α k) * (1 + ‖aVec‖ ^ ∑ k, δ k) :=
    mul_le_mul hx ha (Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _)
      (add_nonneg zero_le_one (pow_nonneg (norm_nonneg _) _))
  simpa [aVec, mul_assoc] using
    mul_le_mul_of_nonneg_right hprod (norm_nonneg (elementaryPartial f β γ xt a b))

/-- A monomial times a partial is bounded by the corresponding Schwartz seminorm. -/
lemma monomial_partial_le_seminorm (α : Fin m → ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (δ : Fin r → ℕ) (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖((∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)) *
        elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm (α, β, γ, δ) f := by
  let z : ℂ := ((∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)) *
      elementaryPartial f β γ xt a b
  have hcoe : (‖z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val (α, β, γ, δ) :=
    le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))
  change ‖z‖ ≤ (elementarySchwartzBound f.val (α, β, γ, δ)).toReal
  rw [← toReal_coe_nnnorm z]
  exact ENNReal.toReal_mono (f.property.2 (α, β, γ, δ)).ne hcoe

lemma prod_abs_pow_single {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (j : ℕ) :
    ∏ k, |x k| ^ (Pi.single i j k) = |x i| ^ j := by
  rw [Finset.prod_eq_single i]
  · simp [Pi.single_eq_same]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk, pow_zero]
  · intro hk
    exact (hk (Finset.mem_univ i)).elim

lemma zero_monomial_partial_le (β : Fin m → ℕ) (γ : Fin n → ℕ) (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖elementaryPartial f β γ xt a b‖ ≤ elementarySchwartzSeminorm (0, β, γ, 0) f := by
  have h := monomial_partial_le_seminorm (0 : Fin m → ℕ) β γ (0 : Fin r → ℕ) f xt a b
  simpa only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul] using h

lemma single_real_partial_le (i : Fin m) (j : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    |xt.1 i| ^ j * ‖elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm (Pi.single i j, β, γ, 0) f := by
  have h := monomial_partial_le_seminorm (Pi.single i j) β γ (0 : Fin r → ℕ) f xt a b
  have hnorm : ‖((∏ k, (xt.1 k : ℂ) ^ (Pi.single i j k)) * (∏ k, (a k : ℂ) ^ (0 : ℕ))) *
        elementaryPartial f β γ xt a b‖ =
      |xt.1 i| ^ j * ‖elementaryPartial f β γ xt a b‖ := by
    rw [norm_mul, norm_mul]
    simp only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast,
      Pi.zero_apply, pow_zero, Finset.prod_const_one, norm_one, mul_one]
    rw [prod_abs_pow_single (fun k => xt.1 k) i j]
  rw [← hnorm]
  exact h

lemma single_int_partial_le (k0 : Fin r) (j' : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm ((0 : Fin m → ℕ), β, γ, Pi.single k0 j') f := by
  have h := monomial_partial_le_seminorm (0 : Fin m → ℕ) β γ (Pi.single k0 j') f xt a b
  have hnorm : ‖((∏ k, (xt.1 k : ℂ) ^ (0 : ℕ)) * (∏ k, (a k : ℂ) ^ (Pi.single k0 j' k))) *
        elementaryPartial f β γ xt a b‖ =
      |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ := by
    rw [norm_mul, norm_mul]
    simp only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast,
      Pi.zero_apply, pow_zero, Finset.prod_const_one, norm_one, one_mul]
    rw [prod_abs_pow_single (fun k => (a k : ℝ)) k0 j']
  rw [← hnorm]
  exact h

lemma single_both_partial_le (i : Fin m) (k0 : Fin r) (j j' : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    |xt.1 i| ^ j * |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm (Pi.single i j, β, γ, Pi.single k0 j') f := by
  have h := monomial_partial_le_seminorm (Pi.single i j) β γ (Pi.single k0 j') f xt a b
  have hnorm : ‖((∏ k, (xt.1 k : ℂ) ^ (Pi.single i j k)) *
        (∏ k, (a k : ℂ) ^ (Pi.single k0 j' k))) * elementaryPartial f β γ xt a b‖ =
      |xt.1 i| ^ j * |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ := by
    rw [norm_mul, norm_mul]
    simp only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast]
    rw [prod_abs_pow_single (fun k => xt.1 k) i j,
      prod_abs_pow_single (fun k => (a k : ℝ)) k0 j']
  rw [← hnorm]
  exact h

/-- Paper: Lemma D.1.3.4, p. 751. Polynomial weights in the two Euclidean lengths,
with a fixed mixed partial for each seminorm, generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P1 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖) := by
  let bound (i : ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)) (f : ElementarySchwartz m n r F) : ℝ≥0∞ :=
    ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
      ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
        (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
        ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖)
  letI : DecidableEq (ElementarySchwartzIndex m n r) := Classical.decEq _
  have hest (i : ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)) :
      ∃ (s : Finset (ElementarySchwartzIndex m n r)) (C : ℝ), 0 ≤ C ∧
        ∀ f, bound i f ≤ ENNReal.ofReal (C * ((s.sup elementarySchwartzSeminorm) f)) := by
    let j := i.1
    let j' := i.2.1
    let β := i.2.2.1
    let γ := i.2.2.2
    let Cx : ℝ := 1 + (Real.sqrt (m : ℝ)) ^ j
    let Ca : ℝ := 1 + (Real.sqrt (r : ℝ)) ^ j'
    let s0 : Finset (ElementarySchwartzIndex m n r) := {(0, β, γ, (0 : Fin r → ℕ))}
    let sx : Finset (ElementarySchwartzIndex m n r) :=
      Finset.univ.image fun t : Fin m => (Pi.single t j, β, γ, (0 : Fin r → ℕ))
    let sy : Finset (ElementarySchwartzIndex m n r) :=
      Finset.univ.image fun t : Fin r => ((0 : Fin m → ℕ), β, γ, Pi.single t j')
    let sz : Finset (ElementarySchwartzIndex m n r) :=
      Finset.univ.image fun q : Fin m × Fin r => (Pi.single q.1 j, β, γ, Pi.single q.2 j')
    let s := ((s0 ∪ sx) ∪ sy) ∪ sz
    let C : ℝ := Cx * Ca * ((m + 1) * (r + 1) : ℝ)
    refine ⟨s, C, by positivity, fun f => ?_⟩
    refine iSup_le fun xt => iSup_le fun a => iSup_le fun b => ?_
    let aVec := (WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))
    let N : ℝ := ‖elementaryPartial f β γ xt a b‖
    let Sx : ℝ := ∑ t : Fin m, |xt.1 t| ^ j
    let Sa : ℝ := ∑ t : Fin r, |aVec t| ^ j'
    let supS : ℝ := (s.sup elementarySchwartzSeminorm) f
    have hx : 1 + ‖xt.1‖ ^ j ≤ Cx * (1 + Sx) := by
      simpa only [Cx, Sx] using one_add_euclidean_pow_le xt.1 j
    have ha : 1 + ‖aVec‖ ^ j' ≤ Ca * (1 + Sa) := by
      simpa only [Ca, Sa] using one_add_euclidean_pow_le aVec j'
    have hcoord (t : Fin r) : aVec t = (a t : ℝ) := by
      simp [aVec]
    have hmem0 : ((0 : Fin m → ℕ), β, γ, (0 : Fin r → ℕ)) ∈ s :=
      Finset.mem_union_left sz (Finset.mem_union_left sy (Finset.mem_union_left sx
        (Finset.mem_singleton_self _)))
    have hmemx (t : Fin m) : (Pi.single t j, β, γ, (0 : Fin r → ℕ)) ∈ s :=
      Finset.mem_union_left sz (Finset.mem_union_left sy (Finset.mem_union_right s0
        (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
    have hmemy (t : Fin r) : ((0 : Fin m → ℕ), β, γ, Pi.single t j') ∈ s :=
      Finset.mem_union_left sz (Finset.mem_union_right (s0 ∪ sx)
        (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
    have hmemz (t : Fin m) (u : Fin r) : (Pi.single t j, β, γ, Pi.single u j') ∈ s :=
      Finset.mem_union_right ((s0 ∪ sx) ∪ sy)
        (Finset.mem_image_of_mem _ (Finset.mem_univ (t, u)))
    have hN : N ≤ supS :=
      (zero_monomial_partial_le β γ f xt a b).trans (Seminorm.le_finset_sup_apply hmem0)
    have hxle (t : Fin m) : |xt.1 t| ^ j * N ≤ supS :=
      (single_real_partial_le t j β γ f xt a b).trans (Seminorm.le_finset_sup_apply (hmemx t))
    have hale (t : Fin r) : |aVec t| ^ j' * N ≤ supS := by
      rw [hcoord t]
      exact (single_int_partial_le t j' β γ f xt a b).trans (Seminorm.le_finset_sup_apply (hmemy t))
    have hboth (t : Fin m) (u : Fin r) : |xt.1 t| ^ j * |aVec u| ^ j' * N ≤ supS := by
      rw [hcoord u]
      exact (single_both_partial_le t u j j' β γ f xt a b).trans
        (Seminorm.le_finset_sup_apply (hmemz t u))
    have hweights : (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤
        Cx * Ca * ((1 + Sx) * (1 + Sa) * N) := by
      have hmul : (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') ≤ (Cx * (1 + Sx)) * (Ca * (1 + Sa)) :=
        mul_le_mul hx ha (by positivity) (by positivity)
      calc
        (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤
            ((Cx * (1 + Sx)) * (Ca * (1 + Sa))) * N :=
          mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
        _ = Cx * Ca * ((1 + Sx) * (1 + Sa) * N) := by ring
    have hexpand : (1 + Sx) * (1 + Sa) * N =
        N + ∑ t : Fin m, |xt.1 t| ^ j * N + ∑ t : Fin r, |aVec t| ^ j' * N +
          ∑ t : Fin m, ∑ u : Fin r, |xt.1 t| ^ j * |aVec u| ^ j' * N := by
      have hSx : Sx * N = ∑ t : Fin m, |xt.1 t| ^ j * N := by simp only [Sx, Finset.sum_mul]
      have hSa : Sa * N = ∑ t : Fin r, |aVec t| ^ j' * N := by simp only [Sa, Finset.sum_mul]
      have hSS : Sx * Sa * N =
          ∑ t : Fin m, ∑ u : Fin r, |xt.1 t| ^ j * |aVec u| ^ j' * N := by
        simp only [Sx, Sa]
        rw [mul_assoc, Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum, ← mul_assoc]
      calc
        (1 + Sx) * (1 + Sa) * N = N + Sx * N + Sa * N + Sx * Sa * N := by ring
        _ = N + ∑ t : Fin m, |xt.1 t| ^ j * N + ∑ t : Fin r, |aVec t| ^ j' * N +
            ∑ t : Fin m, ∑ u : Fin r, |xt.1 t| ^ j * |aVec u| ^ j' * N := by rw [hSx, hSa, hSS]
    have hconst : supS + ∑ _t : Fin m, supS + ∑ _t : Fin r, supS +
        ∑ _t : Fin m, ∑ _u : Fin r, supS = ((m + 1) * (r + 1) : ℝ) * supS := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hsumle : (1 + Sx) * (1 + Sa) * N ≤ ((m + 1) * (r + 1) : ℝ) * supS := by
      rw [hexpand]
      refine (add_le_add (add_le_add (add_le_add hN ?_) ?_) ?_).trans_eq hconst
      · exact Finset.sum_le_sum fun t _ => hxle t
      · exact Finset.sum_le_sum fun t _ => hale t
      · exact Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => hboth t u
    have hfinal : (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤ C * supS := by
      calc
        (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤
            Cx * Ca * ((1 + Sx) * (1 + Sa) * N) := hweights
        _ ≤ Cx * Ca * (((m + 1) * (r + 1) : ℝ) * supS) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
        _ = C * supS := by ring
    have hEnn := ENNReal.ofReal_le_ofReal hfinal
    simpa only [j, j', β, γ, aVec, N, supS] using hEnn
  have hfin (i) (f : ElementarySchwartz m n r F) : bound i f ≠ ⊤ := by
    obtain ⟨_, _, _, hle⟩ := hest i
    exact ((hle f).trans_lt ENNReal.ofReal_lt_top).ne
  have hadd (i) (f g : ElementarySchwartz m n r F) :
      bound i (f + g) ≤ bound i f + bound i g := by
    refine iSup_le fun xt => iSup_le fun a => iSup_le fun b => ?_
    have hp := elementaryPartial_add f.property.1 g.property.1 i.2.2.1 i.2.2.2 xt a b
    set w : ℝ := (1 + ‖xt.1‖ ^ i.1) *
      (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1)
    have hw : 0 ≤ w := by positivity
    have hsum : w * ‖elementaryPartial (↑(f + g)) i.2.2.1 i.2.2.2 xt a b‖ ≤
        w * ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖ +
          w * ‖elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖ := by
      calc
        w * ‖elementaryPartial (↑(f + g)) i.2.2.1 i.2.2.2 xt a b‖ =
            w * ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b +
              elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖ := by
          rw [show elementaryPartial (↑(f + g)) i.2.2.1 i.2.2.2 xt a b =
            elementaryPartial (f.val + g.val) i.2.2.1 i.2.2.2 xt a b by rfl, hp]
        _ ≤ w * (‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖ +
            ‖elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
        _ = w * ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖ +
            w * ‖elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖ := by ring
    refine (ENNReal.ofReal_le_ofReal hsum).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hw (norm_nonneg _))]
    exact add_le_add
      (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)))
      (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)))
  have hsmul (i) (c : ℂ) (f : ElementarySchwartz m n r F) :
      bound i (c • f) = ENNReal.ofReal ‖c‖ * bound i f := by
    have hbody : ∀ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ)
        (b : F),
        ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
          (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
          ‖elementaryPartial (↑(c • f)) i.2.2.1 i.2.2.2 xt a b‖) =
          ENNReal.ofReal ‖c‖ * ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖) := by
      intro xt a b
      have hp := elementaryPartial_smul c f.property.1 i.2.2.1 i.2.2.2 xt a b
      have hfun : elementaryPartial (↑(c • f)) i.2.2.1 i.2.2.2 xt a b =
          elementaryPartial (c • f.val) i.2.2.1 i.2.2.2 xt a b := rfl
      rw [hfun, hp, norm_smul]
      have hcomm : (1 + ‖xt.1‖ ^ i.1) *
          (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            (‖c‖ * ‖elementaryPartial f.val i.2.2.1 i.2.2.2 xt a b‖) =
          ‖c‖ * ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
              ‖elementaryPartial f.val i.2.2.1 i.2.2.2 xt a b‖) := by ring
      rw [hcomm, ENNReal.ofReal_mul (norm_nonneg _)]
    simp_rw [bound, hbody, ENNReal.mul_iSup]
  let p : SeminormFamily ℂ (ElementarySchwartz m n r F)
      (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)) :=
    fun i => Seminorm.of (fun f => (bound i f).toReal)
      (fun f g => by
        calc
          (bound i (f + g)).toReal ≤ (bound i f + bound i g).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin i f, hfin i g⟩) (hadd i f g)
          _ = (bound i f).toReal + (bound i g).toReal :=
            ENNReal.toReal_add (hfin i f) (hfin i g))
      (fun c f => by
        rw [hsmul i c f]
        exact ENNReal.toReal_ofReal_mul ‖c‖ (bound i f) (norm_nonneg c))
  refine ⟨p, ?_, ?_⟩
  · refine elementarySchwartz_withSeminorms.congr
      (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
      (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
    · intro i
      obtain ⟨s, C, hC, hle⟩ := hest i
      refine ⟨s, C, fun f => ?_⟩
      have hreal : (bound i f).toReal ≤ C * ((s.sup elementarySchwartzSeminorm) f) := by
        refine (ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (hle f)).trans_eq ?_
        exact ENNReal.toReal_ofReal (mul_nonneg hC (apply_nonneg _ _))
      change (bound i f).toReal ≤ C * ((s.sup elementarySchwartzSeminorm) f)
      exact hreal
    · intro idx
      let iP : ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ) :=
        (∑ k, idx.1 k, ∑ k, idx.2.2.2 k, idx.2.1, idx.2.2.1)
      refine ⟨{iP}, 1, fun f => ?_⟩
      rw [Finset.sup_singleton, one_mul]
      change elementarySchwartzSeminorm idx f ≤ (bound iP f).toReal
      have hpt : elementarySchwartzBound f.val idx ≤ bound iP f := by
        refine iSup_le fun xt => iSup_le fun a => iSup_le fun b => ?_
        have hle := monomial_norm_le_p1 f.val idx.1 idx.2.1 idx.2.2.1 idx.2.2.2 xt a b
        have hcoe : (‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
            elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖₊ : ℝ≥0∞) =
            ENNReal.ofReal ‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
              elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖ := by
          rw [show ‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
              elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖ =
              (‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
                elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖₊ : ℝ) from rfl,
            ENNReal.ofReal_coe_nnreal]
        rw [hcoe]
        exact (ENNReal.ofReal_le_ofReal hle).trans
          (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)))
      exact ENNReal.toReal_mono (hfin iP f) hpt
  · intro i f
    change ENNReal.ofReal (bound i f).toReal = bound i f
    exact ENNReal.ofReal_toReal (hfin i f)

/-- Evaluating a fixed mixed partial derivative at a fixed point is a continuous linear functional
on the elementary Schwartz space: it is dominated by one defining seminorm. -/
theorem elementaryPartial_evaluation_continuousLinear
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ∃ L : ElementarySchwartz m n r F →L[ℂ] ℂ,
      ∀ f, L f = elementaryPartial f β γ x a b := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let dirs : List X :=
    (List.ofFn (fun k : Fin m ↦ List.replicate (β k) (EuclideanSpace.single k 1, 0))).flatten ++
    (List.ofFn (fun k : Fin n ↦ List.replicate (γ k) (0, EuclideanSpace.single k 1))).flatten
  have hdiff (f : E) := (((f.property.1 a b).of_le
    (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
      exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt (x := x))
  let L : E →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ elementaryPartial f β γ x a b
      map_add' := fun f g ↦ by
        change iteratedFDeriv ℝ dirs.length
          ((fun v ↦ f (elementaryCover v a b)) + (fun v ↦ g (elementaryCover v a b))) x
            dirs.get = _
        rw [iteratedFDeriv_add_apply (hdiff f) (hdiff g), add_apply]
        rfl
      map_smul' := fun c f ↦ by
        change iteratedFDeriv ℝ dirs.length (c • (fun v ↦ f (elementaryCover v a b))) x
          dirs.get = _
        rw [iteratedFDeriv_const_smul_apply (a := c) (hdiff f), smul_apply]
        rfl }
  let i : ElementarySchwartzIndex m n r := (0, β, γ, 0)
  have hdom (f : E) : ‖L f‖ ≤ elementarySchwartzSeminorm i f := by
    have h : (‖L f‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val i := by
      unfold elementarySchwartzBound
      apply le_iSup_of_le x
      apply le_iSup_of_le a
      apply le_iSup_of_le b
      simp [i, L]
    exact ENNReal.toReal_mono (f.property.2 i).ne h
  have hc : Continuous L := by
    apply WithSeminorms.continuous_normedSpace_rng _ elementarySchwartz_withSeminorms L
    refine ⟨{i}, 1, ?_⟩
    intro f
    simp [Seminorm.comp_apply]
    exact (hdom f).trans
      (Finset.le_sup (f := elementarySchwartzSeminorm) (Finset.mem_singleton_self i) f)
  exact ⟨⟨L, hc⟩, fun _ ↦ rfl⟩


omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
/-- A polynomial weight times a mixed partial is bounded by the sum, over the monomials of the
polynomial, of the coefficient norms times the corresponding defining seminorms. -/
theorem elementarySchwartz_polynomial_weight_le_monomial_sum
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (f : ElementarySchwartz m n r F)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) p‖ *
      ‖elementaryPartial f β γ xt a b‖ ≤
    ∑ d ∈ p.support, ‖p.coeff d‖ * elementarySchwartzSeminorm
      (fun k ↦ d (Sum.inl k), β, γ, fun k ↦ d (Sum.inr k)) f := by
  classical
  let e := Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))
  let h := elementaryPartial f β γ xt a b
  let idx (d : (Fin m ⊕ Fin r) →₀ ℕ) : ElementarySchwartzIndex m n r :=
    (fun k ↦ d (Sum.inl k), β, γ, fun k ↦ d (Sum.inr k))
  let weight (d : (Fin m ⊕ Fin r) →₀ ℕ) :=
    (∏ k, (xt.1 k:ℂ)^d (Sum.inl k)) * ∏ k, (a k:ℂ)^d (Sum.inr k)
  have hbound (d) : ‖weight d * h‖ ≤ elementarySchwartzSeminorm (idx d) f := by
    have hb : (‖weight d*h‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val (idx d) :=
      le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))
    exact ENNReal.toReal_mono (f.property.2 (idx d)).ne hb
  have hmono (d : (Fin m ⊕ Fin r) →₀ ℕ) (c : ℂ) :
      MvPolynomial.eval e (MvPolynomial.monomial d c) = c * weight d := by
    rw [MvPolynomial.eval_monomial, d.prod_fintype _ (fun _ ↦ pow_zero _), Fintype.prod_sum_type]
    rfl
  have he : MvPolynomial.eval e p * h = ∑ d ∈ p.support, p.coeff d * (weight d*h) := by
    conv_lhs => rw [p.as_sum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [hmono, mul_assoc]
  change ‖MvPolynomial.eval e p‖ * ‖h‖ ≤ _
  rw [← norm_mul, he]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun d _ ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound d) (norm_nonneg _))


/-- For a polynomial weight and a fixed mixed partial, the supremum of the weighted partial is a
continuous seminorm on the elementary Schwartz space. -/
theorem elementarySchwartz_polynomial_weight_continuous_seminorm
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧
      ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ)
        (b : F),
        ENNReal.ofReal
          (‖MvPolynomial.eval (Sum.elim (fun k ↦ (x.1 k : ℂ)) (fun k ↦ (a k : ℂ))) p‖ *
          ‖elementaryPartial f β γ x a b‖) := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := X × (Fin r → ℤ) × F
  choose L hL using (elementaryPartial_evaluation_continuousLinear (F := F) β γ)
  let c (u : J) :=
    MvPolynomial.eval (Sum.elim (fun k ↦ (u.1.1 k : ℂ)) (fun k ↦ (u.2.1 k : ℂ))) p
  let t (u : J) : Seminorm ℂ E :=
    ‖c u‖₊ • (normSeminorm ℂ ℂ).comp (L u.1 u.2.1 u.2.2).toLinearMap
  let d (v : (Fin m ⊕ Fin r) →₀ ℕ) : ElementarySchwartzIndex m n r :=
    (fun k ↦ v (Sum.inl k), β, γ, fun k ↦ v (Sum.inr k))
  let s (v : (Fin m ⊕ Fin r) →₀ ℕ) : Seminorm ℂ E :=
    ‖p.coeff v‖₊ • elementarySchwartzSeminorm (d v)
  let Q : Seminorm ℂ E := ∑ v ∈ p.support, s v
  have hQ : Continuous Q := Seminorm.continuous_finsetSum (fun v _ ↦
    (elementarySchwartz_withSeminorms.continuous_seminorm (d v)).const_smul ‖p.coeff v‖₊)
  have htv (u : J) (f : E) : t u f = ‖c u‖*‖elementaryPartial f β γ u.1 u.2.1 u.2.2‖ := by
    change ‖c u‖ * ‖L u.1 u.2.1 u.2.2 f‖ = _
    rw [hL]
  have hdom (u : J) : t u ≤ Q := by
    intro f
    rw [htv]
    have he : Q f = ∑ v ∈ p.support, s v f := by
      change FunLike.coeAddMonoidHom _ _ _ (∑ v ∈ p.support, s v) f = _
      rw [map_sum, Finset.sum_apply]; rfl
    rw [he]
    exact elementarySchwartz_polynomial_weight_le_monomial_sum p f β γ u.1 u.2.1 u.2.2
  have hbd : BddAbove (Set.range t) := ⟨Q, by rintro _ ⟨u, rfl⟩; exact hdom u⟩
  let q := ⨆ u : J, t u
  refine ⟨q, Seminorm.continuous_of_le hQ (ciSup_le hdom), ?_⟩
  intro f
  let U := ⨆ (x : X) (a : Fin r → ℤ) (b : F), ENNReal.ofReal (t (x, a, b) f)
  have hU : U < ⊤ := by
    apply lt_of_le_of_lt _ (ENNReal.ofReal_lt_top (r := Q f))
    exact iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦
      ENNReal.ofReal_le_ofReal (hdom (x, a, b) f)
  have eq : ENNReal.ofReal (q f) = U := by
    apply le_antisymm
    · rw [← ENNReal.ofReal_toReal hU.ne]
      apply ENNReal.ofReal_le_ofReal
      rw [show q f = ⨆ u : J, t u f from Seminorm.iSup_apply hbd]
      apply ciSup_le
      rintro ⟨x, a, b⟩
      have h : ENNReal.ofReal (t (x, a, b) f) ≤ U :=
        le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
      simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using ENNReal.toReal_mono hU.ne h
    · apply iSup_le
      intro x; apply iSup_le; intro a; apply iSup_le; intro b
      exact ENNReal.ofReal_le_ofReal (le_ciSup hbd (x, a, b) f)
  rw [eq]
  simp only [U, htv, c]
  rfl


/-- Paper: Lemma D.1.3.4, p. 751. Complex polynomial weights in the real and integer
coordinates, with a fixed mixed partial for each seminorm, generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P2 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        ((Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal
            (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.2.2‖ *
              ‖elementaryPartial f i.1 i.2.1 xt a b‖) := by
  classical
  let I := (Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ
  choose Q hc hv using (fun i : I ↦
    elementarySchwartz_polynomial_weight_continuous_seminorm (F := F) i.2.2 i.1 i.2.1)
  refine ⟨Q, ?_, hv⟩
  let P : SeminormFamily ℂ (ElementarySchwartz m n r F) _ := elementarySchwartzSeminorm
  have hp : WithSeminorms P := elementarySchwartz_withSeminorms
  have cover (i : ElementarySchwartzIndex m n r) : ∃ j : I, P i = Q j := by
    let d : (Fin m ⊕ Fin r) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Sum.elim i.1 i.2.2.2)
    let j : I := (i.2.1, i.2.2.1, MvPolynomial.monomial d 1)
    refine ⟨j, ?_⟩
    ext f
    have he : ENNReal.ofReal (Q j f) = elementarySchwartzBound f.val i := by
      rw [hv]
      unfold elementarySchwartzBound
      apply iSup_congr
      intro x
      apply iSup_congr
      intro a
      apply iSup_congr
      intro b
      dsimp only [j]
      rw [MvPolynomial.eval_monomial, d.prod_fintype _ (fun _ ↦ pow_zero _),
        Fintype.prod_sum_type, one_mul, ← norm_mul, ofReal_norm]
      rfl
    change (elementarySchwartzBound f.val i).toReal = Q j f
    rw [← he, ENNReal.toReal_ofReal (apply_nonneg _ _)]
  apply (SeminormFamily.withSeminorms_iff_nhds_eq_iInf Q).mpr
  apply le_antisymm
  · apply le_iInf
    intro j
    apply Filter.tendsto_iff_comap.mp
    exact (hc j).tendsto' 0 0 (map_zero _)
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf P).mp hp]
    apply le_iInf
    intro i
    obtain ⟨j, hij⟩ := cover i
    rw [hij]
    exact iInf_le _ j


/-- For a polynomial weight and a constant-coefficient polynomial differential operator, the
supremum of the weighted operator is a continuous seminorm on the elementary Schwartz space. -/
private theorem elementarySchwartz_polynomial_operator_continuous_seminorm
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (D : MvPolynomial (Fin m ⊕ Fin n) ℂ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧
      ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ)
        (b : F),
        (‖MvPolynomial.eval (Sum.elim (fun k ↦ (x.1 k : ℂ)) (fun k ↦ (a k : ℂ))) p *
          (∑ d ∈ D.support, D.coeff d *
            elementaryPartial f (fun k ↦ d (.inl k)) (fun k ↦ d (.inr k)) x a b)‖₊ : ℝ≥0∞) := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := X × (Fin r → ℤ) × F
  let V := (Fin m ⊕ Fin n) →₀ ℕ
  let β (v : V) := fun k : Fin m ↦ v (.inl k)
  let γ (v : V) := fun k : Fin n ↦ v (.inr k)
  choose L hL using (fun v : V ↦
    elementaryPartial_evaluation_continuousLinear (F := F) (β v) (γ v))
  choose P hP hval using (fun v : V ↦
    elementarySchwartz_polynomial_weight_continuous_seminorm (F := F) p (β v) (γ v))
  let c (u : J) :=
    MvPolynomial.eval (Sum.elim (fun k ↦ (u.1.1 k : ℂ)) (fun k ↦ (u.2.1 k : ℂ))) p
  let A (u : J) : E →ₗ[ℂ] ℂ :=
    ∑ v ∈ D.support, D.coeff v • (L v u.1 u.2.1 u.2.2).toLinearMap
  let t (u : J) : Seminorm ℂ E := ‖c u‖₊ • (normSeminorm ℂ ℂ).comp (A u)
  let s (v : V) : Seminorm ℂ E := ‖D.coeff v‖₊ • P v
  let Q : Seminorm ℂ E := ∑ v ∈ D.support, s v
  have hQ : Continuous Q :=
    Seminorm.continuous_finsetSum (fun v _ ↦ (hP v).const_smul ‖D.coeff v‖₊)
  have htv (u : J) (f : E) : t u f = ‖c u * (∑ v ∈ D.support, D.coeff v *
      elementaryPartial f (β v) (γ v) u.1 u.2.1 u.2.2)‖ := by
    change ‖c u‖ * ‖A u f‖ = _
    simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      smul_eq_mul, hL, norm_mul]
  have hdom (u : J) : t u ≤ Q := by
    intro f
    have he : Q f = ∑ v ∈ D.support, s v f := by
      change FunLike.coeAddMonoidHom _ _ _ (∑ v ∈ D.support, s v) f = _
      rw [map_sum, Finset.sum_apply]; rfl
    rw [he, htv, Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro v _
    have h : ENNReal.ofReal (‖c u‖ * ‖elementaryPartial f (β v) (γ v) u.1 u.2.1 u.2.2‖) ≤
        ENNReal.ofReal (P v f) := by
      rw [hval]
      exact le_iSup_of_le u.1 (le_iSup_of_le u.2.1 (le_iSup_of_le u.2.2 le_rfl))
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (apply_nonneg _ _)] at h'
    change _ ≤ ‖D.coeff v‖ * P v f
    simp only [norm_mul]
    nlinarith only [mul_le_mul_of_nonneg_left h' (norm_nonneg (D.coeff v))]
  have hbd : BddAbove (Set.range t) := ⟨Q, by rintro _ ⟨u, rfl⟩; exact hdom u⟩
  let q := ⨆ u : J, t u
  refine ⟨q, Seminorm.continuous_of_le hQ (ciSup_le hdom), ?_⟩
  intro f
  let U := ⨆ (x : X) (a : Fin r → ℤ) (b : F), ENNReal.ofReal (t (x, a, b) f)
  have hU : U < ⊤ := by
    apply lt_of_le_of_lt _ (ENNReal.ofReal_lt_top (r := Q f))
    exact iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦
      ENNReal.ofReal_le_ofReal (hdom (x, a, b) f)
  have eq : ENNReal.ofReal (q f) = U := by
    apply le_antisymm
    · rw [← ENNReal.ofReal_toReal hU.ne]
      apply ENNReal.ofReal_le_ofReal
      rw [show q f = ⨆ u : J, t u f from Seminorm.iSup_apply hbd]
      apply ciSup_le
      rintro ⟨x, a, b⟩
      have h : ENNReal.ofReal (t (x, a, b) f) ≤ U :=
        le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
      simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using ENNReal.toReal_mono hU.ne h
    · apply iSup_le
      intro x; apply iSup_le; intro a; apply iSup_le; intro b
      exact ENNReal.ofReal_le_ofReal (le_ciSup hbd (x, a, b) f)
  rw [eq]
  simp only [U, htv, c, ofReal_norm]
  rfl


/-- Paper: Lemma D.1.3.4, p. 751. Polynomial weights applied to
constant-coefficient polynomial differential operators generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P3 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.1 *
            (∑ d ∈ i.2.support, i.2.coeff d * elementaryPartial f
              (fun k ↦ d (.inl k)) (fun k ↦ d (.inr k)) xt a b)‖₊ : ℝ≥0∞) := by
  classical
  let I := MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ
  choose Q hc hv using (fun i : I ↦
    elementarySchwartz_polynomial_operator_continuous_seminorm (F := F) i.1 i.2)
  refine ⟨Q, ?_, hv⟩
  obtain ⟨P, hp, hP⟩ := elementarySchwartz_withSeminorms_P2 (m := m) (n := n) (r := r) (F := F)
  have cover (i : (Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ) :
      ∃ j : I, P i = Q j := by
    let d : (Fin m ⊕ Fin n) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Sum.elim i.1 i.2.1)
    let j : I := (i.2.2, MvPolynomial.monomial d 1)
    refine ⟨j, ?_⟩
    ext f
    have he : ENNReal.ofReal (P i f) = ENNReal.ofReal (Q j f) := by
      rw [hP, hv]
      apply iSup_congr
      intro x
      apply iSup_congr
      intro a
      apply iSup_congr
      intro b
      dsimp only [j]
      simp only [MvPolynomial.support_monomial, one_ne_zero, ite_false, Finset.sum_singleton,
        MvPolynomial.coeff_monomial, ← norm_mul, ofReal_norm]
      simp only [ite_true, one_mul]
      rfl
    simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using congrArg ENNReal.toReal he
  apply (SeminormFamily.withSeminorms_iff_nhds_eq_iInf Q).mpr
  apply le_antisymm
  · apply le_iInf
    intro j
    apply Filter.tendsto_iff_comap.mp
    exact (hc j).tendsto' 0 0 (map_zero _)
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf P).mp hp]
    apply le_iInf
    intro i
    obtain ⟨j, hij⟩ := cover i
    rw [hij]
    exact iInf_le _ j



/-- Paper: Lemma D.1.3.5(1), p. 752. Summing the monomial seminorms with each
multi-index of total degree at most N gives a family of norms generating the topology. -/
theorem elementarySchwartz_withSeminorms_sum :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F) ℕ,
      WithSeminorms p ∧ (∀ N f, p N f = 0 ↔ f = 0) ∧
        ∀ N f, p N f =
          ∑ i : (Fin m → Fin (N + 1)) × (Fin m → Fin (N + 1)) ×
                (Fin n → Fin (N + 1)) × (Fin r → Fin (N + 1)),
            if (∑ k, (i.1 k).val) ≤ N ∧ (∑ k, (i.2.1 k).val) ≤ N ∧
                (∑ k, (i.2.2.1 k).val) ≤ N ∧ (∑ k, (i.2.2.2 k).val) ≤ N then
              elementarySchwartzSeminorm
                (fun k ↦ (i.1 k).val, fun k ↦ (i.2.1 k).val,
                  fun k ↦ (i.2.2.1 k).val, fun k ↦ (i.2.2.2 k).val) f
            else 0 := by
  classical
  let E := ElementarySchwartz m n r F
  let I := (Fin m → ℕ) × (Fin m → ℕ) × (Fin n → ℕ) × (Fin r → ℕ)
  let J (N : ℕ) := (Fin m → Fin (N+1)) × (Fin m → Fin (N+1)) ×
    (Fin n → Fin (N+1)) × (Fin r → Fin (N+1))
  let P : I → Seminorm ℂ E := elementarySchwartzSeminorm
  let idx (N : ℕ) (i : J N) : I :=
    (fun k ↦ (i.1 k).val, fun k ↦ (i.2.1 k).val, fun k ↦ (i.2.2.1 k).val,
      fun k ↦ (i.2.2.2 k).val)
  let good (N : ℕ) (i : I) : Prop := (∑ k, i.1 k) ≤ N ∧ (∑ k, i.2.1 k) ≤ N ∧
    (∑ k, i.2.2.1 k) ≤ N ∧ (∑ k, i.2.2.2 k) ≤ N
  let term (N : ℕ) (i : J N) : Seminorm ℂ E := if good N (idx N i) then P (idx N i) else 0
  let Q (N : ℕ) : Seminorm ℂ E := ∑ i : J N, term N i
  have hp : WithSeminorms P := elementarySchwartz_withSeminorms
  have hm (N : ℕ) (i : J N) (hg : good N (idx N i)) : P (idx N i) ≤ Q N := by
    have h := (Finset.le_sup (f := term N) (Finset.mem_univ i)).trans
      (Seminorm.finset_sup_le_sum (term N) Finset.univ)
    simpa only [Q, term, ite_eq_left hg] using h
  have hdom (i : I) : ∃ N, P i ≤ Q N := by
    let N := (∑ k, i.1 k)+(∑ k, i.2.1 k)+(∑ k, i.2.2.1 k)+(∑ k, i.2.2.2 k)
    have hsum {d : ℕ} (a : Fin d → ℕ) (k : Fin d) : a k ≤ ∑ l, a l :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    let t : J N := (fun k ↦ ⟨i.1 k, by have := hsum i.1 k; dsimp [N]; omega⟩,
      fun k ↦ ⟨i.2.1 k, by have := hsum i.2.1 k; dsimp [N]; omega⟩,
      fun k ↦ ⟨i.2.2.1 k, by have := hsum i.2.2.1 k; dsimp [N]; omega⟩,
      fun k ↦ ⟨i.2.2.2 k, by have := hsum i.2.2.2 k; dsimp [N]; omega⟩)
    have hi : idx N t = i := rfl
    refine ⟨N, hi ▸ hm N t ?_⟩
    rw [hi]; dsimp [good, N]; omega
  refine ⟨Q, ?_, ?_, ?_⟩
  · apply (SeminormFamily.withSeminorms_iff_nhds_eq_iInf Q).mpr
    apply le_antisymm
    · apply le_iInf
      intro N
      apply Filter.tendsto_iff_comap.mp
      have hcont : Continuous (Q N) := by
        apply Seminorm.continuous_finsetSum
        intro i _
        dsimp only [term]
        split_ifs
        · exact hp.continuous_seminorm _
        · exact continuous_const
      exact hcont.tendsto' 0 0 (map_zero _)
    · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf P).mp hp]
      apply le_iInf
      intro i
      obtain ⟨N, hN⟩ := hdom i
      apply le_trans (iInf_le _ N)
      apply Filter.tendsto_iff_comap.mp
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (Filter.tendsto_comap : Filter.Tendsto (Q N) (Filter.comap (Q N) (𝓝 0)) (𝓝 0))
        (fun f ↦ apply_nonneg (P i) f) hN
  · intro N f
    refine ⟨fun hz ↦ ?_, fun h ↦ by simp [h]⟩
    let t : J N := (fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0)
    have ht : good N (idx N t) := by simp [good, idx, t]
    have hq := hm N t ht f
    rw [hz] at hq
    have hzero := le_antisymm hq (apply_nonneg (P (idx N t)) f)
    change (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal = 0 at hzero
    have hfin := (f.property.2 (0, 0, 0, 0)).ne
    have hz' := ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right hfin
    rw [elementarySchwartzBound_zero] at hz'
    apply Subtype.ext
    funext g
    change f.val g = 0
    have hb := le_iSup (fun x ↦ (‖f.val x‖₊ : ℝ≥0∞)) g
    rw [hz'] at hb
    simpa using (le_antisymm hb (by positivity))
  · intro N f
    change FunLike.coeAddMonoidHom _ _ _ (∑ i : J N, term N i) f = _
    rw [map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (term N i) f = if good N (idx N i) then (P (idx N i)) f else 0
    by_cases h : good N (idx N i) <;> simp [term, h]



end
end Masullo
