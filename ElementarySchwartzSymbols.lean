import ElementaryDirectionalDerivatives
import FourierSymbols
import PontryaginBidual
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open Function Set Topology
open scoped BigOperators ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "A" => ElementaryLCAModel m n r F
local notation "Dual" => PontryaginDual (Multiplicative A)

/-- The symbol of one invariant derivative on the dual, pulled back along
canonical bidual evaluation. -/
def elementaryDualSymbol (c : Multiplicative ℝ →ₜ* Dual) (g : A) : ℂ :=
  ((Multiplicative.toAdd (characterSlope c (pontryaginBidualEval (Multiplicative.ofAdd g))) : ℝ) : ℂ) *
    Complex.I

private def elementaryDualSlope (c : Multiplicative ℝ →ₜ* Dual) : A →+ ℝ :=
  ((characterSlope c).comp (pontryaginBidualEval (G := Multiplicative A)).toMonoidHom).toAdditive

omit [DiscreteTopology F] in
private theorem elementaryDualSlope_continuous (c : Multiplicative ℝ →ₜ* Dual) :
    Continuous (elementaryDualSlope c) :=
  continuous_toAdd.comp ((characterSlope_continuous c).comp
    ((pontryaginBidualEval (G := Multiplicative A)).continuous.comp continuous_ofAdd))

private theorem compact_addHom_real_zero {K : Type*} [AddGroup K] [TopologicalSpace K]
    [CompactSpace K] (h : K →+ ℝ) (hc : Continuous h) (x : K) : h x = 0 := by
  obtain ⟨B, hB⟩ := (isCompact_range hc).bddAbove
  have hPow (y : K) (k : ℕ) : (k : ℝ) * h y ≤ B := by
    simpa only [map_nsmul, nsmul_eq_mul] using hB (mem_range_self (k • y))
  have hNonpos (y : K) : h y ≤ 0 := by
    by_contra! hp
    obtain ⟨k, hk⟩ := exists_nat_gt (B / h y)
    exact (not_lt_of_ge (hPow y k)) ((div_lt_iff₀ hp).mp hk)
  have hNeg := hNonpos (-x)
  rw [map_neg, neg_nonpos] at hNeg
  exact le_antisymm (hNonpos x) hNeg

def elementaryGrowthCoordinate (j : Fin m ⊕ Fin r) : A →+ ℝ :=
  match j with
  | .inl i =>
    { toFun := fun g ↦ g.1 i
      map_zero' := rfl
      map_add' _ _ := rfl }
  | .inr i =>
    { toFun := fun g ↦ (g.2.2.1 i : ℝ)
      map_zero' := Int.cast_zero
      map_add' _ _ := Int.cast_add _ _ }

omit [DiscreteTopology F] [Finite F] in
theorem elementaryGrowthCoordinate_continuous (j : Fin m ⊕ Fin r) :
    Continuous (elementaryGrowthCoordinate (F := F) (n := n) j) := by
  cases j with
  | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
  | inr i =>
    have h : Continuous (fun z : ℤ ↦ (z : ℝ)) := continuous_of_discreteTopology
    exact h.comp ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))

omit [DiscreteTopology F] in
/-- A continuous real additive form on the elementary group is a linear
combination of the real and integer coordinate functions. -/
theorem elementary_real_addHom_coordinates (h : A →+ ℝ) (hc : Continuous h) :
    ∃ (l : Fin m → ℝ) (d : Fin r → ℝ), ∀ g : A,
      h g = (∑ i, l i * g.1 i) + ∑ i, d i * (g.2.2.1 i : ℝ) := by
  let H : EuclideanSpace ℝ (Fin m) →+ A :=
    (AddMonoidHom.id _).prod (0 : EuclideanSpace ℝ (Fin m) →+ _)
  let D : (Fin r → ℤ) →+ A :=
    (0 : (Fin r → ℤ) →+ _).prod ((0 : (Fin r → ℤ) →+ _).prod
      ((AddMonoidHom.id _).prod (0 : (Fin r → ℤ) →+ F)))
  let K : (Fin n → AddCircle (1 : ℝ)) × F →+ A :=
    (0 : ((Fin n → AddCircle (1 : ℝ)) × F) →+ _).prod
      ((AddMonoidHom.fst _ _).prod ((0 : ((Fin n → AddCircle (1 : ℝ)) × F) →+ _).prod
        (AddMonoidHom.snd _ _)))
  have hH : Continuous H := continuous_id.prodMk continuous_const
  have hK : Continuous K :=
    continuous_const.prodMk (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  let hR := (h.comp H).toRealLinearMap (hc.comp hH)
  let B := EuclideanSpace.basisFun (Fin m) ℝ
  let hZ := h.comp D
  refine ⟨fun i ↦ hR (B i), fun i ↦ hZ (Pi.single i 1), fun g ↦ ?_⟩
  have hg : H g.1 + D g.2.2.1 + K (g.2.1, g.2.2.2) = g := by
    rcases g with ⟨x, t, a, b⟩
    change (x + 0 + 0, 0 + 0 + t, 0 + a + 0, 0 + 0 + b) = (x, t, a, b)
    simp
  have hk := compact_addHom_real_zero (h.comp K) (hc.comp hK) (g.2.1, g.2.2.2)
  have hparts : h g = hR g.1 + hZ g.2.2.1 := by
    calc
      h g = h (H g.1 + D g.2.2.1 + K (g.2.1, g.2.2.2)) := congrArg h hg.symm
      _ = hR g.1 + hZ g.2.2.1 := by
        rw [map_add, map_add]
        change hR g.1 + hZ g.2.2.1 + (h.comp K) (g.2.1, g.2.2.2) = _
        rw [hk, add_zero]
  rw [hparts]
  congr 1
  · conv_lhs => rw [← B.toBasis.sum_repr g.1]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by
      change (B.repr g.1 i) * hR (B i) = _
      rw [EuclideanSpace.basisFun_repr, mul_comm]
  · let a := g.2.2.1
    change hZ a = _
    conv_lhs => rw [← Finset.univ_sum_single a, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single (M := fun _ : Fin r ↦ ℤ) i (a i) = a i • Pi.single i (1 : ℤ) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [zsmul_eq_mul]
      · simp [Pi.single_eq_of_ne hj]
    rw [he, map_zsmul, zsmul_eq_mul]
    exact mul_comm _ _

def elementaryGrowthVariables (g : A) : Fin m ⊕ Fin r → ℂ :=
  Sum.elim (fun i ↦ (g.1 i : ℂ)) (fun i ↦ (g.2.2.1 i : ℂ))

private theorem elementaryDualSymbol_polynomial (c : Multiplicative ℝ →ₜ* Dual) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ,
      ∀ g : A, elementaryDualSymbol c g = MvPolynomial.eval (elementaryGrowthVariables g) p := by
  obtain ⟨l, d, h⟩ := elementary_real_addHom_coordinates
    (elementaryDualSlope c) (elementaryDualSlope_continuous c)
  refine ⟨((∑ i, MvPolynomial.C (l i : ℂ) * MvPolynomial.X (.inl i)) +
      ∑ i, MvPolynomial.C (d i : ℂ) * MvPolynomial.X (.inr i)) * MvPolynomial.C Complex.I, ?_⟩
  intro g
  change ((elementaryDualSlope c g : ℝ) : ℂ) * Complex.I = _
  rw [h]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    map_mul, map_add, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, elementaryGrowthVariables,
    Sum.elim_inl, Sum.elim_inr]

omit [DiscreteTopology F] in
theorem continuousRealForm_elementaryDualSymbol (h : A →+ ℝ) (hc : Continuous h) :
    ∃ c : Multiplicative ℝ →ₜ* Dual, ∀ g : A,
      elementaryDualSymbol c g = Complex.I * (h g : ℂ) := by
  let χ (t : Multiplicative ℝ) : Dual :=
    { toFun := fun x ↦ Circle.exp (t.toAdd * h x.toAdd)
      map_one' := by change Circle.exp (t.toAdd * h 0) = 1; simp
      map_mul' := fun x y ↦ by
        change Circle.exp (t.toAdd * h (x.toAdd + y.toAdd)) = _
        rw [map_add, mul_add, Circle.exp_add]
      continuous_toFun := Circle.exp.continuous.comp
        (continuous_const.mul (hc.comp continuous_toAdd)) }
  have hχ : Continuous χ := ContinuousMonoidHom.continuous_of_continuous_uncurry χ
    (Circle.exp.continuous.comp ((continuous_toAdd.comp continuous_fst).mul
      ((hc.comp continuous_toAdd).comp continuous_snd)))
  let c : Multiplicative ℝ →ₜ* Dual :=
    { toFun := χ
      map_one' := PontryaginDual.ext fun x ↦ by
        change Circle.exp (0 * h x.toAdd) = _
        simp
      map_mul' := fun t s ↦ PontryaginDual.ext fun x ↦ by
        change Circle.exp ((t.toAdd + s.toAdd) * h x.toAdd) = _
        rw [add_mul, Circle.exp_add]
        rfl
      continuous_toFun := hχ }
  refine ⟨c, fun g ↦ ?_⟩
  have hs := characterSlope_unique c (pontryaginBidualEval (Multiplicative.ofAdd g)) (h g)
    (fun t ↦ by change Circle.exp (t * h g) = Circle.exp (h g * t); rw [mul_comm])
  rw [elementaryDualSymbol, hs, mul_comm]

omit [DiscreteTopology F] in
/-- Each real or lattice coordinate occurs as the symbol of a genuine
one-parameter subgroup of the dual, up to the unit factor i. -/
private theorem elementaryGrowthCoordinate_symbol (j : Fin m ⊕ Fin r) :
    ∃ c : Multiplicative ℝ →ₜ* Dual, ∀ g : A,
      elementaryDualSymbol c g = Complex.I * elementaryGrowthVariables g j := by
  obtain ⟨c, h⟩ := continuousRealForm_elementaryDualSymbol
    (elementaryGrowthCoordinate (F := F) (n := n) j) (elementaryGrowthCoordinate_continuous j)
  exact ⟨c, fun g => by cases j <;> exact h g⟩

omit [DiscreteTopology F] in
/-- The normalized first derivative on the dual is a real linear form
in the real and lattice coordinates. -/
theorem elementaryDualSymbol_exists_realCoefficients (c : Multiplicative ℝ →ₜ* Dual) :
    ∃ v : (Fin m ⊕ Fin r) → ℝ, ∀ g : A,
      elementaryDualSymbol c g =
        Complex.I * ∑ i, (v i : ℂ) * elementaryGrowthVariables g i := by
  obtain ⟨l, d, h⟩ := elementary_real_addHom_coordinates (elementaryDualSlope c)
    (elementaryDualSlope_continuous c)
  refine ⟨Sum.elim l d, fun g => ?_⟩
  change (elementaryDualSlope c g : ℂ) * Complex.I = _
  rw [h, Fintype.sum_sum_type, mul_comm _ Complex.I]
  simp [elementaryGrowthVariables, Complex.ofReal_intCast]

/-- Each coefficient vector is realized by a genuine one-parameter subgroup
of the dual. -/
theorem elementaryDualSymbol_realizes_realCoefficients (v : (Fin m ⊕ Fin r) → ℝ) :
    ∃ c : Multiplicative ℝ →ₜ* Dual, ∀ g : A,
      elementaryDualSymbol c g =
        Complex.I * ∑ i, (v i : ℂ) * elementaryGrowthVariables g i := by
  let h : A →+ ℝ := ∑ i, v i • elementaryGrowthCoordinate (F := F) (n := n) i
  have hc : Continuous h := by
    change Continuous (fun g => (∑ i, v i • elementaryGrowthCoordinate (F := F) (n := n) i) g)
    simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (elementaryGrowthCoordinate_continuous i)
  obtain ⟨c, he⟩ := continuousRealForm_elementaryDualSymbol h hc
  refine ⟨c, fun g => ?_⟩
  rw [he]
  simp only [h, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl i => rfl
  | inr i => simp [elementaryGrowthCoordinate, elementaryGrowthVariables]


/-- The symbol of a word is the product of the first-order symbols. -/
def elementaryDualWord (cs : List (Multiplicative ℝ →ₜ* Dual)) (g : A) : ℂ :=
  (cs.map fun c ↦ elementaryDualSymbol c g).prod

/-- Every polynomial in the real and integer coordinates is a finite linear
combination of symbols of invariant differential words on the dual. -/
theorem elementaryPolynomial_exists_dualWords (P : MvPolynomial (Fin m ⊕ Fin r) ℂ) :
    ∃ Q : List (ℂ × List (Multiplicative ℝ →ₜ* Dual)), ∀ g : A,
      MvPolynomial.eval (elementaryGrowthVariables g) P =
        (Q.map fun (d, ds) => d * elementaryDualWord ds g).sum := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨[(c, [])], fun g => by simp [elementaryDualWord]⟩
  | add P₁ P₂ ih₁ ih₂ =>
    obtain ⟨Q₁, h₁⟩ := ih₁
    obtain ⟨Q₂, h₂⟩ := ih₂
    exact ⟨Q₁ ++ Q₂, fun g => by rw [map_add, h₁, h₂, List.map_append, List.sum_append]⟩
  | mul_X P i ih =>
    obtain ⟨Q, hQ⟩ := ih
    obtain ⟨c, hc⟩ := elementaryGrowthCoordinate_symbol (n := n) (F := F) i
    refine ⟨Q.map (fun (d, ds) => ((-Complex.I) * d, c :: ds)), fun g => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, hQ, ← List.sum_map_mul_right, List.map_map]
    congr 1
    apply List.map_congr_left
    rintro ⟨d, ds⟩ _
    simp only [Function.comp_apply, elementaryDualWord, List.map_cons, List.prod_cons, hc]
    rw [show (-Complex.I * d) * (Complex.I * elementaryGrowthVariables g i *
      (List.map (fun c => elementaryDualSymbol c g) ds).prod) =
        d * (List.map (fun c => elementaryDualSymbol c g) ds).prod * elementaryGrowthVariables g i by
      calc
        _ = (- (Complex.I ^ 2)) *
            (d * (List.map (fun c => elementaryDualSymbol c g) ds).prod * elementaryGrowthVariables g i) := by ring
        _ = _ := by simp [Complex.I_sq]]

/-- The word symbol is evaluation of the corresponding differential operator
on the bidual character at the identity of the dual group. -/
theorem elementaryDualWord_eq_evaluation (cs : List (Multiplicative ℝ →ₜ* Dual)) (g : A) :
    elementaryDualWord cs g =
      (cs.foldr directionalDeriv (fun χ : Dual ↦ (χ (Multiplicative.ofAdd g) : ℂ))) 1 :=
  (directionalDeriv_character_symbol cs
    (pontryaginBidualEval (Multiplicative.ofAdd g))).2.1.symm

theorem elementaryDualWord_polynomial (cs : List (Multiplicative ℝ →ₜ* Dual)) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ,
      ∀ g : A, elementaryDualWord cs g = MvPolynomial.eval (elementaryGrowthVariables g) p := by
  induction cs with
  | nil => exact ⟨1, fun g ↦ by simp [elementaryDualWord]⟩
  | cons c cs ih =>
    obtain ⟨p, hp⟩ := elementaryDualSymbol_polynomial c
    obtain ⟨q, hq⟩ := ih
    exact ⟨p * q, fun g ↦ by simpa only [elementaryDualWord, List.map_cons, List.prod_cons,
      map_mul] using congrArg₂ (· * ·) (hp g) (hq g)⟩

private theorem elementaryDualWord_monomial_norm (α : Fin m → ℕ) (δ : Fin r → ℕ) :
    ∃ cs : List (Multiplicative ℝ →ₜ* Dual), ∀ g : A,
      ‖elementaryDualWord cs g‖ =
        ‖(∏ i, (g.1 i : ℂ) ^ α i) * (∏ i, (g.2.2.1 i : ℂ) ^ δ i)‖ := by
  choose c hc using fun j : Fin m ⊕ Fin r ↦
    elementaryGrowthCoordinate_symbol (F := F) (n := n) j
  let ds := (List.ofFn fun i ↦ List.replicate (α i) (c (.inl i))).flatten ++
    (List.ofFn fun i ↦ List.replicate (δ i) (c (.inr i))).flatten
  refine ⟨ds, fun g ↦ ?_⟩
  have hNorm (j : Fin m ⊕ Fin r) : ‖elementaryDualSymbol (c j) g‖ =
      ‖elementaryGrowthVariables g j‖ := by rw [hc, norm_mul, Complex.norm_I, one_mul]
  simp only [elementaryDualWord, ds, List.map_append, List.prod_append, List.map_flatten,
    List.map_ofFn, List.map_replicate, List.prod_flatten, List.prod_replicate, List.prod_ofFn,
    Function.comp_def, norm_mul, norm_pow, norm_prod, hNorm, elementaryGrowthVariables,
    Sum.elim_inl, Sum.elim_inr]

/-- Each coordinate mixed partial is the lift of a word of genuine
one-parameter derivatives. -/
theorem elementaryOrbitWord_partial (β : Fin m → ℕ) (γ : Fin n → ℕ)
    : ∃ cs : List (Multiplicative ℝ →ₜ* Multiplicative A),
      ∀ (f : A → ℂ) (_hf : ∀ a b, ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b))) x a b,
      elementaryOrbitWord cs f (elementaryCover x a b) = elementaryPartial f β γ x a b := by
  let D := elementaryDirectionList β γ
  let v (i : Fin D.length) := elementaryFibreBasis m n (D.get i)
  refine ⟨List.ofFn (fun i ↦ elementaryOneParameter (r := r) (F := F) (v i)), fun f hf x a b ↦ ?_⟩
  rw [elementaryOrbitWord_tuple _ v (fun _ _ ↦ rfl) f a b (hf a b) x, elementaryPartial_eq_basis]


private theorem elementary_weightedWord_continuous
    (f : A → ℂ) (hf : ∀ a b, ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b)))
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
    (ds : List (Multiplicative ℝ →ₜ* Dual)) :
    Continuous (fun g ↦ elementaryDualWord ds g * elementaryOrbitWord cs f g) := by
  have hD : Continuous (elementaryOrbitWord cs f) := by
    apply elementary_continuous_of_fibres
    intro a b
    obtain ⟨v, hv⟩ := elementaryOrbitWord_cover cs f a b (hf a b)
    rw [funext hv]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin cs.length ↦ X) ℂ v).continuous.comp
      ((hf a b).continuous_iteratedFDeriv (by exact_mod_cast (le_top : (cs.length : ℕ∞) ≤ ⊤)))
  have hS : Continuous (elementaryDualWord ds) := by
    induction ds with
    | nil => exact continuous_const
    | cons c ds ih =>
      exact ((Complex.continuous_ofReal.comp (elementaryDualSlope_continuous c)).mul
        continuous_const).mul ih
  exact hS.mul hD

/-- Each weighted invariant derivative is dominated uniformly by a continuous
seminorm in the original elementary Schwartz topology. -/
theorem elementary_polynomialWord_bound
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) :
    ∃ B : Seminorm ℂ (ElementarySchwartz m n r F), Continuous B ∧
      ∀ (f : ElementarySchwartz m n r F) g,
        ‖MvPolynomial.eval (elementaryGrowthVariables g) p * elementaryOrbitWord cs f g‖ ≤ B f := by
  classical
  choose v hv using fun i : Fin cs.length ↦ elementaryOneParameter_lift (cs.get i)
  let J := Fin m ⊕ Fin n
  let T := Fin cs.length → J
  let E := elementaryFibreBasis m n
  choose β γ hPartial using fun t : T ↦ elementaryIteratedFDeriv_basis (r := r) (F := F) t
  let c (t : T) := ∏ i, E.repr (v i) (t i)
  let q (t : T) (d : (Fin m ⊕ Fin r) →₀ ℕ) : Seminorm ℂ (ElementarySchwartz m n r F) :=
    (‖c t‖₊ : ℝ≥0) • ((‖p.coeff d‖₊ : ℝ≥0) • elementarySchwartzSeminorm
      (fun i ↦ d (.inl i), β t, γ t, fun i ↦ d (.inr i)))
  let B : Seminorm ℂ (ElementarySchwartz m n r F) := ∑ t : T, ∑ d ∈ p.support, q t d
  have hb (f : ElementarySchwartz m n r F) :
      B f = ∑ t : T, |c t| * ∑ d ∈ p.support, ‖p.coeff d‖ * elementarySchwartzSeminorm
        (fun i ↦ d (.inl i), β t, γ t, fun i ↦ d (.inr i)) f := by
    change FunLike.coeAddMonoidHom _ _ _ (∑ t : T, ∑ d ∈ p.support, q t d) f = _
    simp only [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ ↦ by
      change ‖c t‖ * (‖p.coeff d‖ * elementarySchwartzSeminorm
        (fun i ↦ d (.inl i), β t, γ t, fun i ↦ d (.inr i)) f) = _
      rw [Real.norm_eq_abs]
  refine ⟨B, ?_, fun f g ↦ ?_⟩
  · exact Seminorm.continuous_finsetSum fun t _ ↦ Seminorm.continuous_finsetSum fun d _ ↦ by
      change Continuous fun f : ElementarySchwartz m n r F ↦
        ‖c t‖ * (‖p.coeff d‖ * elementarySchwartzSeminorm
          (fun i ↦ d (.inl i), β t, γ t, fun i ↦ d (.inr i)) f)
      exact continuous_const.mul (continuous_const.mul
        (elementarySchwartz_withSeminorms.continuous_seminorm _))
  rw [hb]
  obtain ⟨u, hu⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  let x : X := (g.1, u)
  let a := g.2.2.1
  let b := g.2.2.2
  have hv' : elementaryOrbitWord cs f (elementaryCover x a b) =
      iteratedFDeriv ℝ cs.length (fun w ↦ f (elementaryCover w a b)) x v := by
    simpa only [List.ofFn_get] using elementaryOrbitWord_tuple cs.get v hv f a b (f.property.1 a b) x
  have hg : elementaryCover x a b = g := by
    dsimp [x, a, b] at *
    exact hu
  rw [← hg, hv']
  let D := iteratedFDeriv ℝ cs.length (fun w ↦ f (elementaryCover w a b)) x
  have hD : D v = ∑ t : T, c t • elementaryPartial f (β t) (γ t) x a b := by
    change D.toMultilinearMap v = _
    conv_lhs => rw [show v = (fun i ↦ ∑ j, E.repr (v i) j • E j) from
      funext fun i ↦ (E.sum_repr (v i)).symm]
    rw [D.toMultilinearMap.map_sum]
    simp_rw [D.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe]
    apply Finset.sum_congr rfl
    intro t _
    change c t • D (fun i ↦ E (t i)) = _
    rw [hPartial t f a b (f.property.1 a b) x]
  change ‖MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) p * D v‖ ≤ _
  rw [hD, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
  rw [norm_mul, norm_smul, Real.norm_eq_abs, ← mul_assoc,
    mul_comm ‖MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) p‖, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (elementarySchwartz_polynomial_weight_le_monomial_sum p f (β t) (γ t) x a b) (abs_nonneg _)

theorem elementary_weightedWord_bound
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
    (ds : List (Multiplicative ℝ →ₜ* Dual)) :
    ∃ B : Seminorm ℂ (ElementarySchwartz m n r F), Continuous B ∧
      ∀ (f : ElementarySchwartz m n r F) g,
        ‖elementaryDualWord ds g * elementaryOrbitWord cs f g‖ ≤ B f := by
  obtain ⟨p, hp⟩ := elementaryDualWord_polynomial ds
  simpa only [hp] using elementary_polynomialWord_bound cs p

private theorem elementary_weightedWord_bounded (f : ElementarySchwartz m n r F)
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A)) (ds : List (Multiplicative ℝ →ₜ* Dual)) :
    ∃ B : ℝ, ∀ g, ‖elementaryDualWord ds g * elementaryOrbitWord cs f g‖ ≤ B := by
  obtain ⟨q, _, hq⟩ := elementary_weightedWord_bound cs ds
  exact ⟨q f, hq f⟩

/-- Global continuity and boundedness under all pairs of invariant words
characterize the elementary Schwartz space. -/
private theorem elementarySchwartz_iff_weightedWords (f : A → ℂ)
    (hf : ∀ a b, ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b))) :
    f ∈ elementarySchwartzSubmodule m n r F ↔
      ∀ (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
        (ds : List (Multiplicative ℝ →ₜ* Dual)),
        Continuous (fun g ↦ elementaryDualWord ds g * elementaryOrbitWord cs f g) ∧
        ∃ B : ℝ, ∀ g, ‖elementaryDualWord ds g * elementaryOrbitWord cs f g‖ ≤ B := by
  constructor
  · intro h cs ds
    exact ⟨elementary_weightedWord_continuous f hf cs ds,
      elementary_weightedWord_bounded ⟨f, h⟩ cs ds⟩
  · intro h
    refine ⟨hf, fun i ↦ ?_⟩
    obtain ⟨cs, hcs⟩ := elementaryOrbitWord_partial (r := r) (F := F) i.2.1 i.2.2.1
    obtain ⟨ds, hds⟩ := elementaryDualWord_monomial_norm (n := n) (F := F) i.1 i.2.2.2
    obtain ⟨B, hB⟩ := (h cs ds).2
    refine lt_of_le_of_lt (b := ENNReal.ofReal B) ?_ ENNReal.ofReal_lt_top
    unfold elementarySchwartzBound
    refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have he := hB (elementaryCover x a b)
    rw [norm_mul, hcs f hf, hds] at he
    simpa only [coe_nnnorm, norm_mul, elementaryCover] using he


private theorem continuous_bounded_wordSum {Y I : Type*} [TopologicalSpace Y]
    (W : I → Y → ℂ)
    (hW : ∀ i, Continuous (W i) ∧ ∃ B : ℝ, ∀ y, ‖W i y‖ ≤ B)
    (L : List (ℂ × I)) :
    Continuous (fun y ↦ (L.map fun (c, i) ↦ c * W i y).sum) ∧
      ∃ B : ℝ, ∀ y, ‖(L.map fun (c, i) ↦ c * W i y).sum‖ ≤ B := by
  induction L with
  | nil => exact ⟨continuous_const, 0, fun _ ↦ by simp⟩
  | cons p L ih =>
    obtain ⟨c, i⟩ := p
    obtain ⟨h, C, hC⟩ := hW i
    obtain ⟨h', B, hB⟩ := ih
    refine ⟨(continuous_const.mul h).add h', ‖c‖ * C + B, fun y ↦ ?_⟩
    change ‖c * W i y + (L.map fun (d, j) ↦ d * W j y).sum‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ (hB y))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)

/-- Lemma D.1.6.16. An elementary smooth function is Schwartz exactly when
every invariant polynomial derivative, multiplied by every invariant symbol
from the dual, is continuous and bounded. The polynomials are represented
by finite complex linear combinations of words in real one-parameter derivatives. -/
theorem elementarySchwartz_iff_invariantSymbols (f : A → ℂ)
    (hf : ∀ a b, ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b))) :
    f ∈ elementarySchwartzSubmodule m n r F ↔
      ∀ (P : List (ℂ × List (Multiplicative ℝ →ₜ* Multiplicative A)))
        (Q : List (ℂ × List (Multiplicative ℝ →ₜ* Dual))),
        let w (g : A) := (Q.map fun (d, ds) ↦ d * elementaryDualWord ds g).sum *
          (P.map fun (c, cs) ↦ c * elementaryOrbitWord cs f g).sum
        Continuous w ∧ ∃ B : ℝ, ∀ g, ‖w g‖ ≤ B := by
  rw [elementarySchwartz_iff_weightedWords f hf]
  constructor
  · intro h P Q
    have hp (ds : List (Multiplicative ℝ →ₜ* Dual)) :
        let p (g : A) := elementaryDualWord ds g *
          (P.map fun (c, cs) ↦ c * elementaryOrbitWord cs f g).sum
        Continuous p ∧ ∃ B : ℝ, ∀ g, ‖p g‖ ≤ B := by
      have he (g : A) : elementaryDualWord ds g *
          (P.map fun (c, cs) ↦ c * elementaryOrbitWord cs f g).sum =
          (P.map fun (c, cs) ↦ c * (elementaryDualWord ds g * elementaryOrbitWord cs f g)).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        rintro ⟨c, cs⟩ _
        ring
      simpa only [he] using continuous_bounded_wordSum
        (fun cs g ↦ elementaryDualWord ds g * elementaryOrbitWord cs f g) (fun cs ↦ h cs ds) P
    have he (g : A) :
        (Q.map fun (d, ds) ↦ d * elementaryDualWord ds g).sum *
          (P.map fun (c, cs) ↦ c * elementaryOrbitWord cs f g).sum =
        (Q.map fun (d, ds) ↦ d * (elementaryDualWord ds g *
          (P.map fun (c, cs) ↦ c * elementaryOrbitWord cs f g).sum)).sum := by
      rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      rintro ⟨d, ds⟩ _
      ring
    simpa only [he] using continuous_bounded_wordSum (fun ds g ↦ elementaryDualWord ds g *
      (P.map fun (c, cs) ↦ c * elementaryOrbitWord cs f g).sum) hp Q
  · intro h cs ds
    simpa using h [(1, cs)] [(1, ds)]


private theorem elementaryOrbitWord_append_deriv
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
    (c : Multiplicative ℝ →ₜ* Multiplicative A) (f : A → ℂ) :
    elementaryOrbitWord (cs ++ [c]) f = elementaryOrbitWord cs (elementaryOrbitDeriv c f) := by
  induction cs with
  | nil => rfl
  | cons a cs ih => simp only [List.cons_append, elementaryOrbitWord, ih]

private theorem elementaryOrbitDeriv_smooth (c : Multiplicative ℝ →ₜ* Multiplicative A)
    (f : ElementarySchwartz m n r F) :
    ∀ a b, ContDiff ℝ ∞ (fun x ↦ elementaryOrbitDeriv c f (elementaryCover x a b)) := by
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift c
  intro a b
  have he : (fun x ↦ elementaryOrbitDeriv c f (elementaryCover x a b)) =
      fun x ↦ fderiv ℝ (fun y ↦ f (elementaryCover y a b)) x v := by
    funext x
    exact elementaryOrbitDeriv_cover c v hv f a b x
      ((f.property.1 a b).differentiable (by simp)).differentiableAt
  rw [he]
  exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp
    ((f.property.1 a b).fderiv_right (by simp))

private theorem elementaryOrbitDeriv_bound (c : Multiplicative ℝ →ₜ* Multiplicative A)
    (i : ElementarySchwartzIndex m n r) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧
      ∀ (f : ElementarySchwartz m n r F), elementarySchwartzBound (elementaryOrbitDeriv c f) i ≤ ENNReal.ofReal (q f) := by
  obtain ⟨cs, hcs⟩ := elementaryOrbitWord_partial (r := r) (F := F) i.2.1 i.2.2.1
  obtain ⟨ds, hds⟩ := elementaryDualWord_monomial_norm (n := n) (F := F) i.1 i.2.2.2
  obtain ⟨q, hq, hBound⟩ := elementary_weightedWord_bound (cs ++ [c]) ds
  refine ⟨q, hq, fun f ↦ ?_⟩
  unfold elementarySchwartzBound
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have hb := hBound f (elementaryCover x a b)
  rw [norm_mul, elementaryOrbitWord_append_deriv,
    hcs _ (elementaryOrbitDeriv_smooth c f), hds] at hb
  simpa only [coe_nnnorm, norm_mul, elementaryCover] using hb

/-- Each first-order invariant operator is a continuous complex-linear
endomorphism of the elementary Schwartz space. -/
def elementarySchwartz_derivative (c : Multiplicative ℝ →ₜ* Multiplicative A) :
    ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m n r F := by
  let T : ElementarySchwartz m n r F →ₗ[ℂ] ElementarySchwartz m n r F :=
    { toFun := fun f ↦ ⟨elementaryOrbitDeriv c f, elementaryOrbitDeriv_smooth c f, fun i ↦ by
        obtain ⟨q, _, hq⟩ := elementaryOrbitDeriv_bound c i
        exact (hq f).trans_lt ENNReal.ofReal_lt_top⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ by
        have hf := elementaryOrbit_hasDerivAt c f
          (fun a b ↦ (f.property.1 a b).differentiable (by simp)) x
        have hg := elementaryOrbit_hasDerivAt c g
          (fun a b ↦ (g.property.1 a b).differentiable (by simp)) x
        exact (hf.add hg).deriv)
      map_smul' := fun b f ↦ Subtype.ext (funext fun x ↦ by
        have hf := elementaryOrbit_hasDerivAt c f
          (fun a b ↦ (f.property.1 a b).differentiable (by simp)) x
        exact (hf.const_smul b).deriv) }
  refine ⟨T, ?_⟩
  apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
  intro i
  obtain ⟨q, hq, hBound⟩ := elementaryOrbitDeriv_bound c i
  refine Seminorm.continuous_of_le hq fun f ↦ ?_
  change (elementarySchwartzBound (elementaryOrbitDeriv c f) i).toReal ≤ q f
  simpa only [ENNReal.toReal_ofReal (apply_nonneg q f)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBound f)

@[simp] theorem elementarySchwartz_derivative_apply (c : Multiplicative ℝ →ₜ* Multiplicative A)
    (f : ElementarySchwartz m n r F) (x : A) :
    elementarySchwartz_derivative c f x = elementaryOrbitDeriv c f x := rfl


/-- A word of invariant derivatives acting on elementary Schwartz tests. -/
def elementarySchwartz_derivativeWord (cs : List (Multiplicative ℝ →ₜ* Multiplicative A)) :
    ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m n r F :=
  cs.foldr (fun c D => (elementarySchwartz_derivative c).comp D) (ContinuousLinearMap.id ℂ _)

@[simp] theorem elementarySchwartz_derivativeWord_apply
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
    (f : ElementarySchwartz m n r F) (g : A) :
    elementarySchwartz_derivativeWord cs f g = elementaryOrbitWord cs f g := by
  induction cs generalizing f g with
  | nil => rfl
  | cons c cs ih =>
    change elementaryOrbitDeriv c (elementarySchwartz_derivativeWord cs f) g =
      elementaryOrbitDeriv c (elementaryOrbitWord cs f) g
    rw [funext (ih f)]

local notation "E₀" => ElementarySchwartz m n r F
local notation "Words" => List (Multiplicative ℝ →ₜ* Multiplicative A)
local notation "DualWords" => List (Multiplicative ℝ →ₜ* Dual)

/-- A word of invariant derivatives weighted by a dual symbol, as a
continuous linear map into bounded continuous functions. -/
def elementarySchwartz_weightedWord (cs : Words) (ds : DualWords) : E₀ →L[ℂ] (BoundedContinuousFunction A ℂ) := by
  let q := (elementary_weightedWord_bound cs ds).choose
  have hq := (elementary_weightedWord_bound cs ds).choose_spec.1
  have hb (f : E₀) : ∀ g, ‖elementaryDualWord ds g * elementarySchwartz_derivativeWord cs f g‖ ≤ q f := by
    simpa only [elementarySchwartz_derivativeWord_apply] using
      (elementary_weightedWord_bound cs ds).choose_spec.2 f
  have hc (f : E₀) : Continuous (fun g => elementaryDualWord ds g * elementarySchwartz_derivativeWord cs f g) := by
    simpa only [elementarySchwartz_derivativeWord_apply] using
      elementary_weightedWord_continuous f f.property.1 cs ds
  let T : E₀ →ₗ[ℂ] BoundedContinuousFunction A ℂ :=
    { toFun := fun f =>
        BoundedContinuousFunction.ofNormedAddCommGroup _ (hc f) (q f) (hb f)
      map_add' := fun f k => by
        ext g
        change elementaryDualWord ds g * elementarySchwartz_derivativeWord cs (f + k) g =
          elementaryDualWord ds g * elementarySchwartz_derivativeWord cs f g +
          elementaryDualWord ds g * elementarySchwartz_derivativeWord cs k g
        rw [map_add]
        exact mul_add _ _ _
      map_smul' := fun z f => by
        ext g
        change elementaryDualWord ds g * elementarySchwartz_derivativeWord cs (z • f) g =
          z * (elementaryDualWord ds g * elementarySchwartz_derivativeWord cs f g)
        rw [map_smul]
        exact mul_left_comm _ _ _ }
  refine ⟨T, continuous_of_continuousAt_zero T ?_⟩
  have hbnd (f : E₀) : ‖T f‖ ≤ q f :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg q f) (hb f)
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun f => norm_nonneg (T f)) hbnd (map_zero q ▸ hq.tendsto 0)

@[simp] theorem elementarySchwartz_weightedWord_apply (cs : Words) (ds : DualWords)
    (f : E₀) (g : A) :
    elementarySchwartz_weightedWord cs ds f g =
      elementaryDualWord ds g * elementaryOrbitWord cs f g := by
  unfold elementarySchwartz_weightedWord
  change elementaryDualWord ds g * elementarySchwartz_derivativeWord cs f g = _
  rw [elementarySchwartz_derivativeWord_apply]

/-- The canonical real and torus partials and the real and lattice monomials
give exactly the supremum norms of the associated invariant words. -/
theorem exists_elementarySchwartzSeminorm_eq_weightedWord
    (i : ElementarySchwartzIndex m n r) :
    ∃ (cs : Words) (ds : DualWords), ∀ f : E₀,
      elementarySchwartzSeminorm i f = ‖elementarySchwartz_weightedWord cs ds f‖ := by
  rcases i with ⟨α, β, γ, δ⟩
  obtain ⟨cs, hcs⟩ := elementaryOrbitWord_partial (F := F) (r := r) β γ
  obtain ⟨ds, hds⟩ := elementaryDualWord_monomial_norm (F := F) (n := n) α δ
  refine ⟨cs, ds, fun f => le_antisymm ?_ ?_⟩
  · change (elementarySchwartzBound f.val (α, β, γ, δ)).toReal ≤
      ‖elementarySchwartz_weightedWord cs ds f‖
    apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
    unfold elementarySchwartzBound
    refine iSup_le fun x => iSup_le fun a => iSup_le fun b => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have h := (elementarySchwartz_weightedWord cs ds f).norm_coe_le_norm (elementaryCover x a b)
    rw [elementarySchwartz_weightedWord_apply, norm_mul, hcs _ f.property.1, hds] at h
    simpa only [coe_nnnorm, norm_mul, elementaryCover] using h
  · apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
    rintro ⟨x, z, a, b⟩
    obtain ⟨t, ht⟩ := elementaryCover_surjective a b x z
    rw [← ht, elementarySchwartz_weightedWord_apply, norm_mul, hcs _ f.property.1, hds]
    simpa only [elementaryCover, ← norm_mul] using monomial_partial_le_seminorm α β γ δ f (x, t) a b

/-- The weighted supremum seminorms for invariant differential words
generate the elementary Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_weightedWord :
    WithSeminorms (fun i : Words × DualWords =>
      (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp (elementarySchwartz_weightedWord i.1 i.2).toLinearMap) := by
  classical
  let q (i : Words × DualWords) :=
    (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp (elementarySchwartz_weightedWord i.1 i.2).toLinearMap
  refine elementarySchwartz_withSeminorms.congr
    (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
    (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
  · intro i
    have hq : Continuous (q i) := (elementarySchwartz_weightedWord i.1 i.2).continuous.norm
    obtain ⟨s, C, _, hC⟩ :=
      Seminorm.bound_of_continuous elementarySchwartz_withSeminorms (q i) hq
    exact ⟨s, C, fun f => hC f⟩
  · intro i
    obtain ⟨cs, ds, hi⟩ := exists_elementarySchwartzSeminorm_eq_weightedWord (F := F) i
    refine ⟨{(cs, ds)}, 1, fun f => ?_⟩
    rw [Finset.sup_singleton, one_mul]
    change elementarySchwartzSeminorm i f ≤ ‖elementarySchwartz_weightedWord cs ds f‖
    exact (hi f).le

local notation "Ops" => List (ℂ × Words)
local notation "DualOps" => List (ℂ × DualWords)

/-- A pair of invariant differential polynomials gives a weighted operator
on elementary Schwartz functions. -/
def elementarySchwartz_weightedOperator (P : Ops) (Q : DualOps) :
    E₀ →L[ℂ] BoundedContinuousFunction A ℂ :=
  (Q.map fun (d, ds) => d • (P.map fun (c, cs) =>
    c • elementarySchwartz_weightedWord cs ds).sum).sum

theorem elementarySchwartz_weightedOperator_apply (P : Ops) (Q : DualOps)
    (f : E₀) (g : A) :
    elementarySchwartz_weightedOperator P Q f g =
      (Q.map fun (d, ds) => d * elementaryDualWord ds g).sum *
        (P.map fun (c, cs) => c * elementaryOrbitWord cs f g).sum := by
  have hP (ds : DualWords) :
      ((P.map fun (c, cs) => c • elementarySchwartz_weightedWord cs ds).sum :
        E₀ →L[ℂ] BoundedContinuousFunction A ℂ) f g =
        elementaryDualWord ds g * (P.map fun (c, cs) => c * elementaryOrbitWord cs f g).sum := by
    induction P with
    | nil => simp
    | cons p P ih =>
      rcases p with ⟨c, cs⟩
      simp only [List.map_cons, List.sum_cons, add_apply,
        BoundedContinuousFunction.add_apply, smul_apply,
        BoundedContinuousFunction.smul_apply, smul_eq_mul, elementarySchwartz_weightedWord_apply, ih]
      ring
  unfold elementarySchwartz_weightedOperator
  induction Q with
  | nil => simp
  | cons q Q ih =>
    rcases q with ⟨d, ds⟩
    simp only [List.map_cons, List.sum_cons, add_apply,
      BoundedContinuousFunction.add_apply, smul_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, hP, ih]
    ring

theorem elementarySchwartz_weightedOperator_norm (P : Ops) (Q : DualOps) (f : E₀) :
    ‖elementarySchwartz_weightedOperator P Q f‖ =
      ⨆ g : A, ‖(Q.map fun (d, ds) => d * elementaryDualWord ds g).sum *
        (P.map fun (c, cs) => c * elementaryOrbitWord cs f g).sum‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm]
  simp only [elementarySchwartz_weightedOperator_apply]

/-- The supremum seminorms in D.1.10.6(1), for all pairs of invariant
differential polynomials, give the original elementary Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_weightedOperator :
    WithSeminorms (fun i : Ops × DualOps =>
      (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp
        (elementarySchwartz_weightedOperator i.1 i.2).toLinearMap) := by
  classical
  let p (i : Words × DualWords) := (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp
    (elementarySchwartz_weightedWord i.1 i.2).toLinearMap
  let q (i : Ops × DualOps) := (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp
    (elementarySchwartz_weightedOperator i.1 i.2).toLinearMap
  have hp : WithSeminorms p := elementarySchwartz_withSeminorms_weightedWord
  refine hp.congr (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
    (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
  · intro i
    have hq : Continuous (q i) := (elementarySchwartz_weightedOperator i.1 i.2).continuous.norm
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp (q i) hq
    exact ⟨s, C, fun f => hC f⟩
  · rintro ⟨cs, ds⟩
    refine ⟨{([(1, cs)], [(1, ds)])}, 1, fun f => ?_⟩
    rw [Finset.sup_singleton, one_mul]
    change ‖elementarySchwartz_weightedWord cs ds f‖ ≤
      ‖elementarySchwartz_weightedOperator [(1, cs)] [(1, ds)] f‖
    apply le_of_eq
    congr 1
    ext g
    rw [elementarySchwartz_weightedWord_apply, elementarySchwartz_weightedOperator_apply]
    simp


end

end Masullo
