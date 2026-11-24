import BruhatStagePolynomialSeminorms

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The weighted radial integral against `dt/t` and norm-one Haar measure. The
section takes the logarithm of the positive radial parameter as its input. -/
def bruhatSplitRadialNorm {K : Subgroup G} (τ : Multiplicative ℝ →ₜ* G)
    (ν : Measure K) (p : ℝ≥0∞) (Q : Polynomial ℂ) (u : BruhatSchwartz G) : ℝ :=
  (∫ t in Ioi (0 : ℝ), t⁻¹ * ∫ k,
    ‖Q.eval (↑|Real.log t| : ℂ) *
      u.val (τ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^ p.toReal ∂ν) ^
    (1 / p.toReal)

theorem bruhatSplitRadialNorm_ofReal {K : Subgroup G} (τ : Multiplicative ℝ →ₜ* G)
    (ν : Measure K) {p : ℝ} (hp : 0 ≤ p) (Q : Polynomial ℂ) (u : BruhatSchwartz G) :
    bruhatSplitRadialNorm τ ν (ENNReal.ofReal p) Q u =
      (∫ t in Ioi (0 : ℝ), t⁻¹ * ∫ k,
        ‖Q.eval (↑|Real.log t| : ℂ) *
          u.val (τ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^ p ∂ν) ^ (1 / p) := by
  unfold bruhatSplitRadialNorm
  rw [ENNReal.toReal_ofReal hp]

/-- Polynomial weights of the absolute logarithm can be integrated in the
split Haar measure, with the exact radial `dt/t` formula. -/
theorem lpNorm_logPolynomial_positiveRadial
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsFiniteMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : p ≠ ⊤) (Q : Polynomial ℂ) (u : BruhatSchwartz G) :
    lpNorm (fun g => Q.eval (↑|modulatedLog m g| : ℂ) * u.val g) p
        (modulatedLogMeasure m τ hτ ν) = bruhatSplitRadialNorm τ ν p Q u := by
  let μ := modulatedLogMeasure m τ hτ ν
  letI : μ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
  let F (g : G) := Q.eval (↑|modulatedLog m g| : ℂ) * u.val g
  have hlog := continuous_toAdd.comp m.continuous
  have hF : Continuous F := (Q.continuous.comp (Complex.continuous_ofReal.comp hlog.abs)).mul
    (bruhatSchwartz_continuous u)
  have hmem : MemLp F p μ := by
    change MemLp (fun g => Q.eval (↑|modulatedLog m g| : ℂ) * u.val g) p μ
    clear hF F
    induction Q using Polynomial.induction_on' with
    | add A B hA hB =>
      apply (hA.add hB).ae_eq
      exact ae_of_all μ fun g => by simp only [Pi.add_apply, Polynomial.eval_add, add_mul]
    | monomial n a =>
      apply ((bruhatSchwartz_logPower_memLp μ m hm hτ.surjective hp n u).const_mul a).ae_eq
      exact ae_of_all μ fun g => by simp only [Polynomial.eval_monomial, mul_assoc]
  change lpNorm F p μ = _
  rw [lpNorm_modulatedLogMeasure_positiveRadial m τ hτ ν (zero_lt_one.trans_le hp).ne'
    hfin hF hmem]
  unfold bruhatSplitRadialNorm
  apply congrArg (fun y : ℝ => y ^ (1 / p.toReal))
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  apply congrArg (t⁻¹ * ·)
  apply integral_congr_ae
  refine ae_of_all _ fun k => ?_
  have hmod : modulatedLog m (τ (Multiplicative.ofAdd (Real.log t)) * k.val) =
      Real.log t := by
    rw [modulatedLog, map_mul, hτ _, show m k.val = 1 from k.property, mul_one]
    rfl
  simp only [F, hmod]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- Radial invariant differentiation becomes the Euler operator on the positive
coordinate. This applies to each Schwartz–Bruhat derivative profile. -/
theorem bruhatSchwartz_radialDerivative_eq_euler
    (τ : Multiplicative ℝ →ₜ* G) (u : BruhatSchwartz G) (g : G) {t : ℝ} (ht : 0 < t) :
    (bruhatSchwartz_derivative τ u).val (τ (Multiplicative.ofAdd (Real.log t)) * g) =
      t • deriv (fun s : ℝ => u.val (τ (Multiplicative.ofAdd (Real.log s)) * g)) t := by
  let x := τ (Multiplicative.ofAdd (Real.log t)) * g
  let f (s : ℝ) := u.val (x * τ (Multiplicative.ofAdd s))
  let h (s : ℝ) := Real.log s - Real.log t
  have hf : HasDerivAt f (bruhatOrbitDeriv τ u.val x) 0 :=
    (bruhatOrbitDeriv_regular τ u.val (s := 0) (bruhatSchwartz_le_smooth u.property 1)).2 x
  have hh : HasDerivAt h t⁻¹ t := (Real.hasDerivAt_log ht.ne').sub_const _
  have hcomp := hf.scomp_of_eq t hh (show 0 = h t by simp [h])
  have he : f ∘ h = fun s : ℝ => u.val (τ (Multiplicative.ofAdd (Real.log s)) * g) := by
    funext s
    change u.val ((τ (Multiplicative.ofAdd (Real.log t)) * g) *
      τ (Multiplicative.ofAdd (Real.log s - Real.log t))) = _
    rw [mul_right_comm, ← map_mul]
    have hs : Multiplicative.ofAdd (Real.log t) * Multiplicative.ofAdd (Real.log s - Real.log t) =
        Multiplicative.ofAdd (Real.log s) := by
      apply Multiplicative.toAdd.injective
      change Real.log t + (Real.log s - Real.log t) = Real.log s
      ring
    rw [hs]
  change bruhatOrbitDeriv τ u.val x = _
  rw [← he, hcomp.deriv, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- A radial word of order `r` acts by the `r`-fold Euler operator on the
positive radial restriction of the angularly differentiated test. -/
theorem bruhatSchwartz_radialWord_eq_euler_iterate
    (τ : Multiplicative ℝ →ₜ* G) (u : BruhatSchwartz G) (g : G)
    (cs : List (Multiplicative ℝ →ₜ* G)) (r : ℕ) {t : ℝ} (ht : 0 < t) :
    (WholeBruhatStage.bruhatDerivativeWord (List.replicate r τ ++ cs) u).val
        (τ (Multiplicative.ofAdd (Real.log t)) * g) =
      (fun v : ℝ → ℂ => fun s : ℝ => s • deriv v s)^[r]
        (fun s : ℝ => (WholeBruhatStage.bruhatDerivativeWord cs u).val
          (τ (Multiplicative.ofAdd (Real.log s)) * g)) t := by
  let E (v : ℝ → ℂ) (s : ℝ) := s • deriv v s
  let w (s : ℝ) := (WholeBruhatStage.bruhatDerivativeWord cs u).val
    (τ (Multiplicative.ofAdd (Real.log s)) * g)
  change _ = (E^[r] w) t
  induction r generalizing t with
  | zero => rfl
  | succ r ih =>
    let v := WholeBruhatStage.bruhatDerivativeWord (List.replicate r τ ++ cs) u
    rw [List.replicate_succ, List.cons_append, Function.iterate_succ_apply']
    change (bruhatSchwartz_derivative τ v).val (τ (Multiplicative.ofAdd (Real.log t)) * g) =
      t • deriv (E^[r] w) t
    rw [bruhatSchwartz_radialDerivative_eq_euler τ v g ht]
    have he : (fun s : ℝ => v.val (τ (Multiplicative.ofAdd (Real.log s)) * g)) =ᶠ[𝓝 t]
        E^[r] w :=
      (eventually_gt_nhds ht).mono fun s hs => ih hs
    exact congrArg (t • ·) he.deriv_eq

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- Splitting the multiplicities into a radial order and angular orders has
exactly the ordering used in the manuscript's derivative monomial. -/
theorem invariantBasisWord_map_finCons {d : ℕ} (m : ℕ) (α : Fin d → ℕ)
    (γ : Fin (d + 1) → Multiplicative ℝ →ₜ* G) :
    (invariantBasisWord (Fin.cons m α)).map γ =
      List.replicate m (γ 0) ++ (invariantBasisWord α).map (γ ∘ Fin.succ) := by
  simp only [invariantBasisWord, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
    List.flatten_cons, List.map_append, List.map_replicate, List.map_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.map_replicate]

namespace WholeBruhatStage

/-- The three split-Haar seminorm families and the topology they generate. The
multi-index records the radial order in position zero and the angular orders
in the remaining positions when the radial section is the first direction. -/
def HasSplitRadialSeminorms (P : WholeBruhatStage G) {K : Subgroup G}
    (τ : Multiplicative ℝ →ₜ* G) (ν : Measure K) (p : ℝ≥0∞)
    {d : ℕ} (γ : Fin d → Multiplicative ℝ →ₜ* G) : Prop :=
    let D a (f : P.fixedSubmodule) := bruhatDerivativeWord ((invariantBasisWord a).map γ) f.val
    ∃ M U : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × ℕ),
    ∃ Q : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × Polynomial ℂ),
      WithSeminorms M ∧ WithSeminorms U ∧ WithSeminorms Q ∧
      (∀ a n f, M (a, n) f = bruhatSplitRadialNorm τ ν p (Polynomial.monomial n 1) (D a f)) ∧
      (∀ a n f, U (a, n) f = bruhatSplitRadialNorm τ ν p (1 + Polynomial.monomial n 1) (D a f)) ∧
      (∀ a q f, Q (a, q) f = bruhatSplitRadialNorm τ ν p q (D a f))

/-- All three explicit split-Haar seminorm families generate the inherited
topology on a fixed Bruhat stage with the projected directions forming a basis. -/
theorem withSeminorms_fixed_splitRadialLp (P : WholeBruhatStage G)
    [MeasurableSpace P.val.2.finiteFactor] [BorelSpace P.val.2.finiteFactor]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (K : Subgroup G) (hK : m.toMonoidHom.ker = K)
    (ν : Measure K) [ν.IsHaarMeasure] [IsFiniteMeasure ν]
    {d : ℕ} (B : Module.Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (γ : Fin d → Multiplicative ℝ →ₜ* G)
    (hγ : ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (B i))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hfin : p ≠ ⊤) :
    P.HasSplitRadialSeminorms τ ν p γ := by
  subst K
  dsimp only [HasSplitRadialSeminorms]
  let μ := modulatedLogMeasure m τ hτ ν
  letI : μ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
  obtain ⟨M, U, Q, hM, hU, hQ, hMn, hUn, hQn⟩ :=
    P.withSeminorms_fixed_polynomialLp μ m hm hτ.surjective B γ hγ p
  refine ⟨M, U, Q, hM, hU, hQ, ?_, ?_, ?_⟩
  · intro a n f
    rw [hMn, ← lpNorm_logPolynomial_positiveRadial m hm τ hτ ν Fact.out hfin]
    simp only [Polynomial.eval_monomial, one_mul, μ]
  · intro a n f
    rw [hUn, ← lpNorm_logPolynomial_positiveRadial m hm τ hτ ν Fact.out hfin]
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_monomial, one_mul, μ]
  · intro a q f
    rw [hQn]
    exact lpNorm_logPolynomial_positiveRadial m hm τ hτ ν Fact.out hfin q _

end WholeBruhatStage

end
end Masullo
