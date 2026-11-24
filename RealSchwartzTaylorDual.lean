import RealSchwartzBorelJets
import FinestReflexivity
import QuotientDuals
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.Support

open Filter Function LineDeriv Set Topology
open scoped Polynomial SchwartzMap

namespace Masullo

noncomputable section

/-- Precomposition with a continuous linear equivalence identifies strong duals. -/
def strongDualPrecompEquiv {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (e : X ≃L[ℂ] Y) : StrongDual ℂ Y ≃L[ℂ] StrongDual ℂ X :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.precomp ℂ e.toContinuousLinearMap)
    (ContinuousLinearMap.precomp ℂ e.symm.toContinuousLinearMap)
    (fun l ↦ ContinuousLinearMap.ext fun y ↦ by simp)
    (fun l ↦ ContinuousLinearMap.ext fun x ↦ by simp)

private abbrev S := 𝓢(ℝ, ℂ)
private abbrev Q := S ⧸ realSchwartzTaylor.ker

/-- The strong dual of the real Schwartz Taylor quotient is the polynomial
space with its finest locally convex topology. -/
def realSchwartzTaylorStrongDual :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    ℂ[X] ≃L[ℂ] StrongDual ℂ Q := by
  letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
  let b := Polynomial.basisMonomials ℂ
  exact (finest_strongBidual b).trans
    ((strongDualPrecompEquiv (finest_strongDual_product b)).trans
      (strongDualPrecompEquiv realSchwartzTaylorQuotient))

/-- Its monomial basis evaluates the normalized derivatives at zero.
With the distributional sign convention, the (n)-th vector represents
((-1)^n/n!) times the (n)-th Dirac derivative. -/
theorem realSchwartzTaylorStrongDual_monomial (n : ℕ) (f : S) :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    realSchwartzTaylorStrongDual (Polynomial.monomial n 1)
      (realSchwartzTaylor.ker.mkQ f) =
        (n.factorial : ℂ)⁻¹ * realSchwartzJet n f := by
  let b := Polynomial.basisMonomials ℂ
  change finest_strongBidual b (b n) (finest_strongDual_product b
    (realSchwartzTaylorQuotient (realSchwartzTaylor.ker.mkQ f))) = _
  rw [finest_strongBidual_apply, finest_strongDual_product_apply_basis,
    realSchwartzTaylorQuotient_mkQ]
  rfl

/-- The sign relating the coefficient evaluation to the actual derivative
of the Dirac distribution. -/
theorem realDiracDerivative_apply (n : ℕ) (f : S) :
    ((fun T : 𝓢'(ℝ, ℂ) ↦ lineDerivOp (1 : ℝ) T)^[n])
        (TemperedDistribution.delta 0) f = (-1 : ℂ) ^ n * realSchwartzJet n f := by
  induction n generalizing f with
  | zero =>
    rw [Function.iterate_zero_apply, TemperedDistribution.delta_apply, pow_zero, one_mul,
      realSchwartzJet_apply, iteratedDeriv_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', TemperedDistribution.lineDerivOp_apply_apply,
      ih, map_neg, pow_succ]
    have h : (lineDerivOp (1 : ℝ) f : ℝ → ℂ) = deriv (f : ℝ → ℂ) := by
      funext x
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, deriv]
    rw [realSchwartzJet_apply, h, ← iteratedDeriv_succ', ← realSchwartzJet_apply]
    ring

/-- The finite expansion uses iterated distributional derivatives of the
Dirac distribution under the usual transpose sign convention. -/
theorem pointTemperedDistribution_eq_sum_DiracDerivatives
    (T : StrongDual ℂ S) (hT : Distribution.dsupport (⇑T) ⊆ {0}) :
    ∃ N, ∃ c : Fin (N+1) → ℂ, ∀ f : S,
      T f = ∑ j : Fin (N+1), c j *
        (((fun A : 𝓢'(ℝ, ℂ) ↦ lineDerivOp (1 : ℝ) A)^[j.val])
          (TemperedDistribution.delta 0) f) := by
  obtain ⟨N, a, ha⟩ := pointTemperedDistribution_eq_sum_of_dsupport T hT
  refine ⟨N, fun j ↦ a j * (-1 : ℂ) ^ j.val, fun f ↦ (ha f).trans ?_⟩
  apply Finset.sum_congr rfl
  intro j _
  rw [realDiracDerivative_apply]
  symm
  calc
    _ = (a j * ((-1 : ℂ) ^ j.val * (-1 : ℂ) ^ j.val)) * realSchwartzJet j.val f := by ring
    _ = _ := by rw [← mul_pow]; norm_num

private def polynomialAlternateSigns :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    ℂ[X] ≃L[ℂ] ℂ[X] := by
  letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
  letI : PolynormableSpace ℂ ℂ[X] := (finest_withSeminorms ℂ[X]).toPolynormableSpace
  let b := Polynomial.basisMonomials ℂ
  let L := b.constr ℂ (fun n ↦ (-1 : ℂ) ^ n • b n)
  have hL (n : ℕ) : L (b n) = (-1 : ℂ) ^ n • b n := b.constr_basis ℂ _ n
  have h : Function.LeftInverse L L := by
    have he : L.comp L = LinearMap.id := b.ext fun n ↦ by
      change L (L (b n)) = b n
      rw [hL, map_smul, hL, smul_smul, ← mul_pow]
      norm_num
    intro p
    exact DFunLike.congr_fun he p
  let A : ℂ[X] →L[ℂ] ℂ[X] := ⟨L, finest_linear_continuous L⟩
  exact ContinuousLinearEquiv.equivOfInverse A A h h

/-- The polynomial model with the manuscript's Dirac-derivative basis. -/
def realSchwartzDiracStrongDual :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    ℂ[X] ≃L[ℂ] StrongDual ℂ Q := by
  letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
  exact polynomialAlternateSigns.trans realSchwartzTaylorStrongDual

theorem realSchwartzDiracStrongDual_monomial (n : ℕ) (f : S) :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    realSchwartzDiracStrongDual (Polynomial.monomial n 1) (realSchwartzTaylor.ker.mkQ f) =
      (n.factorial : ℂ)⁻¹ * (((fun T : 𝓢'(ℝ, ℂ) ↦ lineDerivOp (1 : ℝ) T)^[n])
        (TemperedDistribution.delta 0) f) := by
  have hs : polynomialAlternateSigns (Polynomial.monomial n 1) =
      (-1 : ℂ) ^ n • Polynomial.monomial n 1 := by
    change (Polynomial.basisMonomials ℂ).constr ℂ _ ((Polynomial.basisMonomials ℂ) n) = _
    rw [(Polynomial.basisMonomials ℂ).constr_basis]
    rfl
  change realSchwartzTaylorStrongDual (polynomialAlternateSigns (Polynomial.monomial n 1))
    (realSchwartzTaylor.ker.mkQ f) = _
  rw [hs, map_smul, smul_apply, realSchwartzTaylorStrongDual_monomial,
    realDiracDerivative_apply, smul_eq_mul]
  ring

/-- The normalized Dirac derivatives determine the polynomial map uniquely. -/
theorem realSchwartzDiracStrongDual_unique :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    ∀ A : ℂ[X] →L[ℂ] StrongDual ℂ Q,
      (∀ n : ℕ, ∀ f : S, A (Polynomial.monomial n 1) (realSchwartzTaylor.ker.mkQ f) =
        (n.factorial : ℂ)⁻¹ * (((fun T : 𝓢'(ℝ, ℂ) ↦ lineDerivOp (1 : ℝ) T)^[n])
          (TemperedDistribution.delta 0) f)) →
      A = realSchwartzDiracStrongDual.toContinuousLinearMap := by
  letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
  intro A hA
  have h : A.toLinearMap = realSchwartzDiracStrongDual.toLinearMap :=
    (Polynomial.basisMonomials ℂ).ext fun n ↦ by
      apply ContinuousLinearMap.ext
      intro q
      obtain ⟨f, rfl⟩ := realSchwartzTaylor.ker.mkQ_surjective q
      exact (hA n f).trans (realSchwartzDiracStrongDual_monomial n f).symm
  exact ContinuousLinearMap.ext fun p ↦ DFunLike.congr_fun h p

/-- For a nonzero polynomial the order of the corresponding distribution
is its degree, in the sense of a bound on all compact test stages. -/
theorem realSchwartzDiracStrongDual_order (p : ℂ[X]) (hp : p ≠ 0) (M : ℕ) :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    testDistributionOrderLE
      (((realSchwartzDiracStrongDual p).comp realSchwartzTaylor.ker.mkQL).comp smoothTestToSchwartz)
      M ↔ p.natDegree ≤ M := by
  letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
  let D := (realSchwartzDiracStrongDual p).comp realSchwartzTaylor.ker.mkQL
  let c (j : Fin (p.natDegree + 1)) :=
    p.coeff j.val * ((j.val.factorial : ℂ)⁻¹ * (-1 : ℂ) ^ j.val)
  have he (f : S) : D f = ∑ j : Fin (p.natDegree+1), c j * realSchwartzJet j.val f := by
    let ev : StrongDual ℂ Q →L[ℂ] ℂ :=
      { toFun := fun T ↦ T (realSchwartzTaylor.ker.mkQ f)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        cont := continuous_eval_const (realSchwartzTaylor.ker.mkQ f) }
    let A := ev.comp realSchwartzDiracStrongDual.toContinuousLinearMap
    change A p = _
    conv_lhs => rw [p.as_sum_range]
    rw [map_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    change realSchwartzDiracStrongDual (Polynomial.monomial j.val (p.coeff j.val))
      (realSchwartzTaylor.ker.mkQ f) = _
    rw [show Polynomial.monomial j.val (p.coeff j.val) =
      p.coeff j.val • Polynomial.monomial j.val (1 : ℂ) by simp [Polynomial.smul_monomial],
      map_smul, smul_apply, realSchwartzDiracStrongDual_monomial,
      realDiracDerivative_apply, smul_eq_mul]
    dsimp [c]
    ring
  change testDistributionOrderLE (D.comp smoothTestToSchwartz) M ↔ _
  rw [pointTemperedDistribution_order_iff D p.natDegree M c he]
  constructor
  · intro h
    by_contra hm
    have hz := h ⟨p.natDegree, Nat.lt_succ_self _⟩ (lt_of_not_ge hm)
    have hd : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hf : (p.natDegree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact (mul_ne_zero hd (mul_ne_zero (inv_ne_zero hf) (pow_ne_zero _ (by norm_num)))) hz
  · intro hm j hj
    exact False.elim ((not_lt_of_ge ((Nat.le_of_lt_succ j.isLt).trans hm)) hj)

/-- Pullback identifies the polynomial model with the annihilator of the
flat Schwartz tests in the continuous dual. -/
theorem realSchwartzDiracStrongDual_range :
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    range (fun p : ℂ[X] ↦ (realSchwartzDiracStrongDual p).comp realSchwartzTaylor.ker.mkQL) =
      {T : StrongDual ℂ S | ∀ f ∈ realSchwartzTaylor.ker, T f = 0} := by
  letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
  rw [show (fun p : ℂ[X] ↦ (realSchwartzDiracStrongDual p).comp realSchwartzTaylor.ker.mkQL) =
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ realSchwartzTaylor.ker.mkQL) ∘
      realSchwartzDiracStrongDual from rfl, range_comp,
    realSchwartzDiracStrongDual.surjective.range_eq, image_univ]
  exact quotientDual_strongRange realSchwartzTaylor.ker

/-- The monomials converge coefficientwise to zero, yet their values at
one stay constant. Thus finite-prefix coefficient seminorms give a
strictly coarser topology on polynomials than the finest one. -/
theorem polynomial_coefficientwise_not_finest :
    (∀ k : ℕ, Filter.Tendsto (fun n : ℕ ↦ (Polynomial.monomial n (1 : ℂ)).coeff k)
      Filter.atTop (𝓝 0)) ∧
    letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    ¬ Filter.Tendsto (fun n : ℕ ↦ Polynomial.monomial n (1 : ℂ)) Filter.atTop (𝓝 0) := by
  constructor
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop k] with n hn
    simp [Polynomial.coeff_monomial, Ne.symm (Nat.ne_of_lt hn)]
  · letI : TopologicalSpace ℂ[X] := finestLocallyConvexTopology ℂ[X]
    intro h
    have he := (finest_linear_continuous (Polynomial.leval (1 : ℂ))).continuousAt.tendsto.comp h
    have h₁ : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℂ)) Filter.atTop (𝓝 0) := by
      simp only [Function.comp_def, Polynomial.leval_apply, Polynomial.eval_monomial,
        Polynomial.eval_zero, one_pow, mul_one] at he
      exact he
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h₁)

end
end Masullo
