import ComplexSchwartzBorelJets
import ComplexPointTemperedExpansion
import RealSchwartzTaylorDual
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Algebra.MvPolynomial.Degrees

open Filter Function Set Topology
open scoped SchwartzMap Distributions MvPowerSeries.WithPiTopology

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℂ, ℂ)
private abbrev Q := S ⧸ complexSchwartzTaylor.ker
private abbrev P := MvPolynomial (Fin 2) ℂ

private def phaseUnit (p : ℕ × ℕ) : ℂˣ := (-1 : ℂˣ) ^ (p.1+p.2)

private def mixedMonomialBasis : Module.Basis (ℕ × ℕ) ℂ P :=
  (AddMonoidAlgebra.basis (Fin 2 →₀ ℕ) ℂ).reindex complexTaylorMultiIndex

private def signedMonomialBasis : Module.Basis (ℕ × ℕ) ℂ P :=
  mixedMonomialBasis.unitsSMul phaseUnit

private theorem signedMonomialBasis_apply (p : ℕ × ℕ) :
    signedMonomialBasis p = (-1 : ℂ) ^ (p.1+p.2) •
      MvPolynomial.monomial (complexTaylorMultiIndex.symm p) 1 := by
  rw [signedMonomialBasis, Module.Basis.unitsSMul_apply, Units.smul_def]
  rw [phaseUnit, Units.val_pow_eq_pow_val, mixedMonomialBasis, Module.Basis.reindex_apply,
    AddMonoidAlgebra.basis_apply]
  rfl

/-- With the finest locally convex topology, bivariate polynomials model
the strong dual of the complex Schwartz Taylor quotient. -/
def complexSchwartzDiracStrongDual :
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    P ≃L[ℂ] StrongDual ℂ Q := by
  letI : TopologicalSpace P := finestLocallyConvexTopology P
  exact (finest_strongBidual signedMonomialBasis).trans
    ((strongDualPrecompEquiv (finest_strongDual_product signedMonomialBasis)).trans
      (strongDualPrecompEquiv complexSchwartzTaylorQuotient))

private theorem complexSchwartzTaylorQuotient_apply (f : S) (p : ℕ × ℕ) :
    complexSchwartzTaylorQuotient (complexSchwartzTaylor.ker.mkQ f) p =
      ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹ * complexSchwartzPointJet p.1 p.2 f := rfl

/-- The monomial of bidegree (a,b) pairs by the factorial-normalized
signed mixed derivative of the test at zero. -/
theorem complexSchwartzDiracStrongDual_monomial (p : ℕ × ℕ) (f : S) :
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    complexSchwartzDiracStrongDual (MvPolynomial.monomial (complexTaylorMultiIndex.symm p) 1)
      (complexSchwartzTaylor.ker.mkQ f) =
      ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹ *
        ((-1 : ℂ) ^ (p.1+p.2) * complexSchwartzPointJet p.1 p.2 f) := by
  letI : TopologicalSpace P := finestLocallyConvexTopology P
  have hbase : complexSchwartzDiracStrongDual (signedMonomialBasis p)
      (complexSchwartzTaylor.ker.mkQ f) =
      ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹ * complexSchwartzPointJet p.1 p.2 f := by
    change finest_strongBidual signedMonomialBasis (signedMonomialBasis p)
      (finest_strongDual_product signedMonomialBasis
        (complexSchwartzTaylorQuotient (complexSchwartzTaylor.ker.mkQ f))) = _
    rw [finest_strongBidual_apply, finest_strongDual_product_apply_basis,
      complexSchwartzTaylorQuotient_apply]
  let c : ℂ := (-1 : ℂ) ^ (p.1+p.2)
  have hc : c * c = 1 := by dsimp [c]; rw [← mul_pow]; norm_num
  have he : MvPolynomial.monomial (complexTaylorMultiIndex.symm p) (1 : ℂ) =
      c • signedMonomialBasis p := by
    rw [signedMonomialBasis_apply, ← show c = (-1 : ℂ) ^ (p.1+p.2) from rfl,
      smul_smul, hc, one_smul]
  rw [he, map_smul, smul_apply, hbase, smul_eq_mul]
  dsimp [c]
  ring

/-- The two transpose signs in the mixed distributional derivative of Dirac. -/
def complexDiracPointDerivative (a b : ℕ) : StrongDual ℂ S :=
  (-1 : ℂ) ^ (a+b) • complexSchwartzPointJet a b

/-- Taking the two negative transposes and applying them to Dirac gives the
signed mixed jet. The negative operators here act on the test argument. -/
theorem complexDiracPointDerivative_apply (a b : ℕ) (f : S) :
    complexDiracPointDerivative a b f =
      (TemperedDistribution.delta (0 : ℂ))
        (((-complexWirtingerZ) ^ a * (-complexWirtingerBar) ^ b) f) := by
  have h (A : S →L[ℂ] S) (n : ℕ) : (-A) ^ n = (-1 : ℂ) ^ n • A ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (-A) ^ (n+1) = ((-1 : ℂ) ^ n • A ^ n) * ((-1 : ℂ) • A) := by
          rw [pow_succ, ih, neg_one_smul]
        _ = (-1 : ℂ) ^ (n+1) • A ^ (n+1) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_succ, ← pow_succ]
  rw [h, h, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]
  rfl

/-- A tempered distribution supported at zero is a finite linear combination
of mixed derivatives of Dirac. -/
theorem complexPointTemperedDistribution_eq_sum_DiracDerivatives
    (T : StrongDual ℂ S) (hT : Distribution.dsupport (⇑T) ⊆ {0}) :
    ∃ N, ∃ c : (ℕ × ℕ) → ℂ,
      T = ∑ p ∈ complexPointJetIndices N, c p • complexDiracPointDerivative p.1 p.2 := by
  obtain ⟨N, a, ha⟩ := complexPointTemperedDistribution_eq_sum_WirtingerJets T hT
  refine ⟨N, fun p ↦ a p * (-1 : ℂ) ^ (p.1+p.2), ?_⟩
  ext f
  rw [ha, sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  simp only [complexDiracPointDerivative, smul_smul, smul_apply, smul_eq_mul]
  rw [mul_assoc (a p), ← mul_pow]
  norm_num

/-- The kernel of the Taylor map is the common kernel of all the mixed
Dirac derivatives. -/
theorem mem_complexSchwartzTaylor_ker_iff (f : S) :
    f ∈ complexSchwartzTaylor.ker ↔ ∀ a b, complexDiracPointDerivative a b f = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h a b
    have he := congrFun h (a,b)
    change (((a.factorial : ℂ) * (b.factorial : ℂ))⁻¹ *
      complexSchwartzPointJet a b f) = 0 at he
    have ha : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
    have hb : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
    rw [complexDiracPointDerivative, smul_apply, (mul_eq_zero.mp he).resolve_left
      (inv_ne_zero (mul_ne_zero ha hb)), smul_zero]
  · intro h
    funext p
    have he := h p.1 p.2
    change (-1 : ℂ) ^ (p.1+p.2) * complexSchwartzPointJet p.1 p.2 f = 0 at he
    change (((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹ *
      complexSchwartzPointJet p.1 p.2 f) = 0
    rw [(mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num)), mul_zero]

/-- The common kernel of the mixed Dirac derivatives is closed. -/
theorem isClosed_complexSchwartzTaylor_ker :
    IsClosed (complexSchwartzTaylor.ker : Set S) := complexSchwartzTaylor.isClosed_ker

/-- Pullback identifies polynomials with the annihilator of flat Schwartz tests. -/
theorem complexSchwartzDiracStrongDual_range :
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    range (fun p : P ↦ (complexSchwartzDiracStrongDual p).comp complexSchwartzTaylor.ker.mkQL) =
      {T : StrongDual ℂ S | ∀ f ∈ complexSchwartzTaylor.ker, T f = 0} := by
  letI : TopologicalSpace P := finestLocallyConvexTopology P
  rw [show (fun p : P ↦ (complexSchwartzDiracStrongDual p).comp complexSchwartzTaylor.ker.mkQL) =
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ complexSchwartzTaylor.ker.mkQL) ∘
      complexSchwartzDiracStrongDual from rfl, range_comp,
    complexSchwartzDiracStrongDual.surjective.range_eq, image_univ]
  exact quotientDual_strongRange complexSchwartzTaylor.ker

/-- The assignment on normalized mixed Dirac derivatives determines the map. -/
theorem complexSchwartzDiracStrongDual_unique :
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    ∀ A : P →L[ℂ] StrongDual ℂ Q,
      (∀ p : ℕ × ℕ, ∀ f : S,
        A (MvPolynomial.monomial (complexTaylorMultiIndex.symm p) 1)
            (complexSchwartzTaylor.ker.mkQ f) =
          ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹ *
            complexDiracPointDerivative p.1 p.2 f) →
      A = complexSchwartzDiracStrongDual.toContinuousLinearMap := by
  letI : TopologicalSpace P := finestLocallyConvexTopology P
  intro A hA
  have h : A.toLinearMap = complexSchwartzDiracStrongDual.toLinearMap :=
    mixedMonomialBasis.ext fun p ↦ by
      apply ContinuousLinearMap.ext
      intro q
      obtain ⟨f, rfl⟩ := complexSchwartzTaylor.ker.mkQ_surjective q
      rw [mixedMonomialBasis, Module.Basis.reindex_apply, AddMonoidAlgebra.basis_apply]
      change A (MvPolynomial.monomial (complexTaylorMultiIndex.symm p) 1) _ = _
      exact (hA p f).trans (complexSchwartzDiracStrongDual_monomial p f).symm
  exact ContinuousLinearMap.ext fun p ↦ DFunLike.congr_fun h p

private theorem totalDegree_multiIndex (s : Fin 2 →₀ ℕ) :
    (s.sum fun _ e ↦ e) = (complexTaylorMultiIndex s).1 + (complexTaylorMultiIndex s).2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fin.sum_univ_two]
  rfl

private theorem complexSchwartzDiracStrongDual_supported (p : P) :
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    Distribution.dsupport (⇑((complexSchwartzDiracStrongDual p).comp
      complexSchwartzTaylor.ker.mkQL)) ⊆ {0} := by
  letI : TopologicalSpace P := finestLocallyConvexTopology P
  intro z hz
  apply (Distribution.mem_dsupport_iff _).mp hz {0} _ isClosed_singleton
  intro f hf
  have hloc := notMem_tsupport_iff_eventuallyEq.mp
    (show 0 ∉ tsupport f from fun h ↦ hf h rfl)
  have hflat : ∀ j : ℕ, iteratedFDeriv ℝ j (f : ℂ → ℂ) 0 = 0 := by
    intro j
    simpa using (hloc.iteratedFDeriv ℝ j).eq_of_nhds
  have hker := (mem_complexSchwartzTaylor_ker_iff f).mpr fun a b ↦ by
    have he := (complexSchwartzPointJet_vanishing_iff (a+b) f).mpr
      (fun j _ ↦ hflat j) a b le_rfl
    simp [complexDiracPointDerivative, he]
  change complexSchwartzDiracStrongDual p (complexSchwartzTaylor.ker.mkQ f) = 0
  have hzero : complexSchwartzTaylor.ker.mkQ f = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hker
  rw [hzero, map_zero]

/-- Polynomial total degree gives the distributional order bound on every
compact test stage. -/
theorem complexSchwartzDiracStrongDual_order (p : P) (M : ℕ) :
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    testDistributionOrderLE
      (((complexSchwartzDiracStrongDual p).comp complexSchwartzTaylor.ker.mkQL).comp
        smoothTestToSchwartz) M ↔ p.totalDegree ≤ M := by
  classical
  letI : TopologicalSpace P := finestLocallyConvexTopology P
  let D := (complexSchwartzDiracStrongDual p).comp complexSchwartzTaylor.ker.mkQL
  let c (q : ℕ × ℕ) := p.coeff (complexTaylorMultiIndex.symm q) *
    (((q.1.factorial : ℂ) * (q.2.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ (q.1+q.2))
  let B := p.support.map complexTaylorMultiIndex.toEmbedding
  have hB : B ⊆ complexPointJetIndices p.totalDegree := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hq
    rw [mem_complexPointJetIndices, Equiv.toEmbedding_apply, ← totalDegree_multiIndex]
    exact MvPolynomial.le_totalDegree hs
  have he (f : S) : D f = ∑ q ∈ complexPointJetIndices p.totalDegree,
      c q * complexSchwartzPointJet q.1 q.2 f := by
    calc
      D f = ∑ q ∈ B, c q * complexSchwartzPointJet q.1 q.2 f := by
        let ev : StrongDual ℂ Q →ₗ[ℂ] ℂ :=
          { toFun := fun T ↦ T (complexSchwartzTaylor.ker.mkQ f)
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
        let A := ev.comp complexSchwartzDiracStrongDual.toLinearMap
        change A p = _
        conv_lhs => rw [p.as_sum]
        rw [map_sum, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro s _
        change complexSchwartzDiracStrongDual (MvPolynomial.monomial s (p.coeff s))
          (complexSchwartzTaylor.ker.mkQ f) = _
        have hm : MvPolynomial.monomial s (p.coeff s) =
            p.coeff s • MvPolynomial.monomial s (1 : ℂ) := by simp [MvPolynomial.smul_monomial]
        rw [hm, map_smul, smul_apply, smul_eq_mul,
          ← complexTaylorMultiIndex.symm_apply_apply s, complexSchwartzDiracStrongDual_monomial]
        simp only [c, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
        ring
      _ = _ := by
        apply Finset.sum_subset hB
        intro q _ hq
        have hq' : complexTaylorMultiIndex.symm q ∉ p.support := fun hs ↦ hq
          (Finset.mem_map.mpr ⟨_, hs, complexTaylorMultiIndex.apply_symm_apply q⟩)
        dsimp [c]
        rw [MvPolynomial.notMem_support_iff.mp hq', zero_mul, zero_mul]
  change testDistributionOrderLE (D.comp smoothTestToSchwartz) M ↔ _
  rw [complexPointTemperedDistribution_order_iff D (complexSchwartzDiracStrongDual_supported p)
    p.totalDegree M c he]
  constructor
  · intro h
    apply Finset.sup_le
    intro s hs
    rw [totalDegree_multiIndex]
    by_contra! hl
    let q := complexTaylorMultiIndex s
    have hq : q ∈ B := Finset.mem_map.mpr ⟨s, hs, rfl⟩
    have hz := h q (hB hq) hl
    have hc : p.coeff (complexTaylorMultiIndex.symm q) ≠ 0 := by
      simpa [q] using MvPolynomial.mem_support_iff.mp hs
    have h₁ : (q.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h₂ : (q.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact (mul_ne_zero hc (mul_ne_zero (inv_ne_zero (mul_ne_zero h₁ h₂))
      (pow_ne_zero _ (by norm_num)))) hz
  · intro h q hq hl
    exact (not_lt_of_ge (((mem_complexPointJetIndices _ _).mp hq).trans h) hl).elim

/-- Increasing powers of the first variable converge coefficientwise to
zero, while evaluation at (1,1) separates them from zero in the finest
locally convex topology. -/
theorem bivariatePolynomial_coefficientwise_not_finest :
    (∀ d : Fin 2 →₀ ℕ, Tendsto
      (fun n : ℕ ↦ (MvPolynomial.monomial (Finsupp.single (0 : Fin 2) n) (1 : ℂ)).coeff d)
        atTop (𝓝 0)) ∧
    letI : TopologicalSpace P := finestLocallyConvexTopology P
    ¬ Tendsto (fun n : ℕ ↦ MvPolynomial.monomial (Finsupp.single (0 : Fin 2) n) (1 : ℂ)) atTop (𝓝 0) := by
  classical
  constructor
  · intro d
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (d 0)] with n hn
    have hne : Finsupp.single (0 : Fin 2) n ≠ d := by
      intro h
      have he := DFunLike.congr_fun h (0 : Fin 2)
      rw [Finsupp.single_eq_same] at he
      omega
    simp [MvPolynomial.coeff_monomial, hne]
  · letI : TopologicalSpace P := finestLocallyConvexTopology P
    intro h
    let ev := (MvPolynomial.aeval (R := ℂ) (fun _ : Fin 2 ↦ (1 : ℂ))).toLinearMap
    have he := (finest_linear_continuous ev).continuousAt.tendsto.comp h
    change Tendsto ((MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℂ))) ∘
      (fun n : ℕ ↦ MvPolynomial.monomial (Finsupp.single (0 : Fin 2) n) (1 : ℂ))) atTop
      (𝓝 (MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℂ)) 0)) at he
    simp [Function.comp_def, MvPolynomial.eval_monomial] at he

/-- The finite total-degree prefixes give the coefficient topology on
formal power series, as characterized by convergence along every filter. -/
theorem bivariatePowerSeries_tendsto_iff_finite_prefix {ι : Type*}
    (F : ι → MvPowerSeries (Fin 2) ℂ) (l : Filter ι) (g : MvPowerSeries (Fin 2) ℂ) :
    Tendsto F l (𝓝 g) ↔ ∀ N : ℕ, ∀ ε > (0 : ℝ),
      ∀ᶠ i in l, ∀ p ∈ complexPointJetIndices N,
        ‖MvPowerSeries.coeff (complexTaylorMultiIndex.symm p) (F i) -
          MvPowerSeries.coeff (complexTaylorMultiIndex.symm p) g‖ < ε := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  constructor
  · intro h N ε hε
    rw [eventually_all_finset]
    intro p _
    simpa only [dist_eq_norm] using
      Metric.tendsto_nhds.mp (h (complexTaylorMultiIndex.symm p)) ε hε
  · intro h d
    rw [Metric.tendsto_nhds]
    intro ε hε
    let p := complexTaylorMultiIndex d
    filter_upwards [h (p.1+p.2) ε hε] with i hi
    have hp := hi p ((mem_complexPointJetIndices _ _).mpr le_rfl)
    simpa only [p, Equiv.symm_apply_apply, dist_eq_norm] using hp

end
end Masullo
