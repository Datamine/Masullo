/-
Differentiation of parameterized stage integrals adapts RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at 1d8742feacca560ae3a2beedfb0e743b1efd8bfe
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import BruhatFourierStages
import ElementarySchwartzCutoffs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ContDiff ENNReal

namespace Masullo

noncomputable section

/-- Differentiation under the integral for a family closed under all
directional derivatives and locally dominated in the parameter. -/
theorem integral_family_fderiv_locallyDominated {V T X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace X] (ν : Measure X) (F : T → V → X → ℂ)
    (hInt : ∀ t u, Integrable (F t u) ν)
    (hd : ∀ t u x, DifferentiableAt ℝ (fun v => F t v x) u)
    (D : T → V → T) (hD : ∀ t u x v, fderiv ℝ (fun w => F t w x) u v = F (D t v) u x)
    (hb : ∀ t u, ∃ b : X → ℝ, Integrable b ν ∧ ∀ᶠ w in 𝓝 u, ∀ x, ‖F t w x‖ ≤ b x) :
    (∀ t, ContDiff ℝ ∞ (fun u => ∫ x, F t u x ∂ν)) ∧
      ∀ t u v, fderiv ℝ (fun w => ∫ x, F t w x ∂ν) u v = ∫ x, F (D t v) u x ∂ν := by
  classical
  let I := Fin (Module.finrank ℝ V)
  let B := Module.finBasis ℝ V
  let ℓ (i : I) := (ContinuousLinearMap.proj i).comp B.equivFunL.toContinuousLinearMap
  let d t u x := fderiv ℝ (fun w => F t w x) u
  have hmeas (t u) : AEStronglyMeasurable (d t u) ν := by
    have he (x) : d t u x = ∑ i : I, (ContinuousLinearMap.smulRightL ℝ V ℂ (ℓ i))
        (F (D t (B i)) u x) := by
      ext v
      change d t u x v = _
      conv_lhs => rw [← B.sum_repr v, map_sum]
      simp only [map_smul, sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
      exact Finset.sum_congr rfl fun i _ => congrArg ((B.repr v i) • ·) (hD t u x (B i))
    rw [show d t u = _ from funext he]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (ContinuousLinearMap.smulRightL ℝ V ℂ (ℓ i)).continuous.comp_aestronglyMeasurable
        (hInt _ _).aestronglyMeasurable
  have hcalc (t u) : HasFDerivAt (fun w => ∫ x, F t w x ∂ν) (∫ x, d t u x ∂ν) u ∧
      Integrable (d t u) ν := by
    obtain ⟨c, -, hB⟩ := B.exists_opNorm_le (F := ℂ)
    choose b hi hle using fun i : I => hb (D t (B i)) u
    let bound (x : X) := c * ∑ i : I, |b i x|
    have hbi : Integrable bound ν := (integrable_finsetSum _ fun i _ => (hi i).abs).const_mul _
    have hdom : ∀ᶠ w in 𝓝 u, ∀ x, ‖d t w x‖ ≤ bound x := by
      filter_upwards [eventually_all.mpr hle] with w hw x
      apply hB (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      intro i
      exact ((hD t w x (B i) ▸ hw i x).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun i => |b i x|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    refine ⟨hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := {w | ∀ x, ‖d t w x‖ ≤ bound x})
      (bound := bound) hdom (.of_forall fun w => (hInt t w).aestronglyMeasurable)
      (hInt t u) (hmeas t u) (.of_forall fun x w hw => hw x)
      hbi (.of_forall fun x w _ => (hd t w x).hasFDerivAt), ?_⟩
    exact hbi.mono' (hmeas t u) (.of_forall (mem_of_mem_nhds hdom))
  have hval (t u v) : fderiv ℝ (fun w => ∫ x, F t w x ∂ν) u v = ∫ x, F (D t v) u x ∂ν := by
    rw [(hcalc t u).1.fderiv, ContinuousLinearMap.integral_apply (hcalc t u).2]
    exact integral_congr_ae (.of_forall fun x => hD t u x v)
  refine ⟨fun t => contDiff_infty.mpr (fun n => ?_), hval⟩
  induction n generalizing t with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun u => (hcalc t u).1.continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_fderiv_apply.mpr
    refine ⟨fun u => (hcalc t u).1.differentiableAt, by simp, fun v => ?_⟩
    simp only [hval]
    exact ih _

/-- Applying one more direction at the end of the list differentiates the
function in that direction before the other iterated derivatives. -/
theorem iteratedFDeriv_append_singleton {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (u v : V) (D : List V) :
    iteratedFDeriv ℝ (D ++ [v]).length f u (D ++ [v]).get =
      iteratedFDeriv ℝ D.length (fun y => fderiv ℝ f y v) u D.get := by
  let eval (s : Σ k, Fin k → V) := iteratedFDeriv ℝ s.1 f u s.2
  have hEval := congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨D.length + 1, Fin.snoc D.get v⟩)
  change iteratedFDeriv ℝ (List.ofFn (Fin.snoc D.get v)).length f u (List.ofFn (Fin.snoc D.get v)).get = _ at hEval
  have hList : List.ofFn (Fin.snoc D.get v) = D ++ [v] := by
    rw [List.ofFn_succ', Fin.snoc_last, List.concat_eq_append]
    simp only [Fin.snoc_castSucc, List.ofFn_get]
  rw [hList] at hEval
  rw [hEval]
  change iteratedFDeriv ℝ (D.length + 1) f u (Fin.snoc D.get v) = _
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  change _ = iteratedFDeriv ℝ D.length ((ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ f) u D.get
  rw [(ContinuousLinearMap.apply ℝ ℂ v).iteratedFDeriv_comp_left
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt
    (by exact_mod_cast (le_top : (D.length : ℕ∞) ≤ ⊤))]
  rfl

private theorem vectorCharacter_phase {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (χ : PontryaginDual (Multiplicative V)) :
    ∃ L : V →L[ℝ] ℝ, ∀ x : V, χ (Multiplicative.ofAdd x) = Circle.exp (L x) := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hE (a b : AddCircle (1 : ℝ)) : e (a + b) = e a * e b := by
    simp only [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
  let c : V →+ AddCircle (1 : ℝ) :=
    { toFun := fun x => e.symm (χ (Multiplicative.ofAdd x))
      map_zero' := by
        apply e.injective
        rw [e.apply_symm_apply]
        change χ 1 = e 0
        simp [e, AddCircle.homeomorphCircle_apply]
      map_add' := fun x y => by
        apply e.injective
        rw [hE, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
        exact map_mul χ (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) }
  have hc : Continuous c := e.symm.continuous.comp (χ.continuous.comp continuous_ofAdd)
  obtain ⟨L, hL, hLift⟩ := exists_addCircle_addMonoidHom_lift c hc
  refine ⟨(2 * Real.pi) • (L.toRealLinearMap hL).toContinuousLinearMap, fun x => ?_⟩
  have h := congrArg e (hLift x)
  change e (L x : AddCircle (1 : ℝ)) = e (e.symm (χ (Multiplicative.ofAdd x))) at h
  rw [e.apply_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
    div_one] at h
  exact h.symm

section Charts

variable {m n r : ℕ} {K : Type*} [AddCommGroup K] [TopologicalSpace K] [DiscreteTopology K]
  [Finite K]
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace X]

local notation "E" => ElementaryLCAModel m n r K
local notation "S" => ElementarySchwartz m n r K
local notation "A" => Multiplicative E

set_option maxHeartbeats 900000 in
/-- On an affine vector family of characters, every iterated Fourier
derivative is another integral with a Schwartz test on the same stage.
The replacement test is independent of the base character. -/
theorem elementaryFourier_charts (ν : Measure X) (q : X → E)
    (α : Multiplicative V →ₜ* PontryaginDual A)
    (hi : ∀ s : S, Integrable (fun x => s (q x)) ν)
    (hm : ∀ ψ : PontryaginDual A,
      AEStronglyMeasurable (fun x => (ψ (Multiplicative.ofAdd (q x)) : ℂ)) ν) :
    let Ψ (s : S) (χ : PontryaginDual A) (u : V) :=
      ∫ x, s (q x) * star ((χ * α (Multiplicative.ofAdd u)) (Multiplicative.ofAdd (q x)) : ℂ) ∂ν
    (∀ s χ, ContDiff ℝ ∞ (Ψ s χ)) ∧
      ∀ (dirs : List V) (s : S), ∃ t : S, ∀ χ u,
        iteratedFDeriv ℝ dirs.length (Ψ s χ) u dirs.get = Ψ t χ u := by
  classical
  intro Ψ
  let F (χ : PontryaginDual A) (s : S) (u : V) (x : X) :=
    s (q x) * star ((χ * α (Multiplicative.ofAdd u)) (Multiplicative.ofAdd (q x)) : ℂ)
  let line (v : V) := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let direction (v : V) : Multiplicative ℝ →ₜ* PontryaginDual A := α.comp
    ⟨(line v).toLinearMap.toAddMonoidHom.toMultiplicative, (line v).continuous⟩
  choose ρ hρ using fun v => exists_frequency_dualDirection (direction v)
  let l (v : V) : E →+ ℝ := (ρ v).toMonoidHom.toAdditive
  have hl (v : V) : Continuous (l v) := (ρ v).continuous
  let D (s : S) (v : V) : S :=
    (-Complex.I) • ⟨_, elementarySchwartz_mul_realHom (l v) (hl v) s⟩
  let ψ (x : X) : PontryaginDual (Multiplicative V) :=
    (pontryaginBidualEval (Multiplicative.ofAdd (q x))).comp α
  choose L hL using fun x => vectorCharacter_phase (ψ x)
  have hphase (x : X) (u : V) :
      α (Multiplicative.ofAdd u) (Multiplicative.ofAdd (q x)) = Circle.exp (L x u) :=
    hL x u
  have hfreq (x : X) (v : V) : L x v = l v (q x) := by
    let β := (ContinuousLinearMap.id ℝ ℝ).smulRight v
    let βm : Multiplicative ℝ →ₜ* Multiplicative V :=
      ⟨β.toLinearMap.toAddMonoidHom.toMultiplicative, β.continuous⟩
    have h₁ := characterSlope_unique βm (ψ x) (L x v) (fun t => by
      change α (Multiplicative.ofAdd (t • v)) (Multiplicative.ofAdd (q x)) = _
      rw [hphase, map_smul, smul_eq_mul, mul_comm])
    have h₂ := characterSlope_unique βm (ψ x) (l v (q x))
      (fun t => hρ v t (Multiplicative.ofAdd (q x)))
    exact h₁.symm.trans h₂
  have he (χ : PontryaginDual A) (s : S) (x : X) :
      (fun u => F χ s u x) = fun u => (s (q x) * star (χ (Multiplicative.ofAdd (q x)) : ℂ)) *
        Complex.exp (-Complex.I * (L x u : ℂ)) := by
    funext u
    dsimp only [F]
    rw [show ((χ * α (Multiplicative.ofAdd u)) (Multiplicative.ofAdd (q x)) : Circle) =
        χ (Multiplicative.ofAdd (q x)) * α (Multiplicative.ofAdd u) (Multiplicative.ofAdd (q x)) from rfl,
      hphase, Circle.coe_mul, star_mul, Circle.coe_exp,
      Complex.star_def, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have hcalc (χ : PontryaginDual A) :
      (∀ s, ContDiff ℝ ∞ (Ψ s χ)) ∧
        ∀ s u v, fderiv ℝ (Ψ s χ) u v = Ψ (D s v) χ u := by
    have hderiv (s : S) (u : V) (x : X) :
        HasFDerivAt (fun w => F χ s w x)
          ((F χ s u x * -Complex.I) • (Complex.ofRealCLM.comp (L x))) u := by
      let C := Complex.ofRealCLM.comp (L x)
      let c := s (q x) * star (χ (Multiplicative.ofAdd (q x)) : ℂ)
      rw [he]
      have h := ((-Complex.I • C).hasFDerivAt.cexp).const_mul c (x := u)
      have hval : F χ s u x = c * Complex.exp (-Complex.I * (L x u : ℂ)) := congrFun (he χ s x) u
      simpa only [c, C, hval, smul_apply, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply, smul_eq_mul, smul_smul, mul_assoc] using h
    apply integral_family_fderiv_locallyDominated ν (F χ) ?_ (fun s u x => (hderiv s u x).differentiableAt) D ?_ ?_
    · intro s u
      refine (hi s).norm.mono' ((hi s).aestronglyMeasurable.mul (hm _).star) (.of_forall fun x => ?_)
      simp only [F, norm_mul, norm_star, Circle.norm_coe, mul_one, le_rfl]
    · intro s u x v
      rw [(hderiv s u x).fderiv]
      change (F χ s u x * -Complex.I) * (L x v : ℂ) = F χ (D s v) u x
      rw [hfreq]
      simp only [F, D, Complex.real_smul]
      change (s (q x) * _ * -Complex.I) * (l v (q x) : ℂ) =
        (-Complex.I * ((l v (q x) : ℂ) * s (q x))) * _
      ring
    · intro s u
      exact ⟨fun x => ‖s (q x)‖, (hi s).norm, .of_forall fun u x => by
        simp only [F, norm_mul, norm_star, Circle.norm_coe, mul_one, le_rfl]⟩
  refine ⟨fun s χ => (hcalc χ).1 s, fun dirs => ?_⟩
  induction dirs using List.reverseRecOn with
  | nil => exact fun s => ⟨s, fun χ u => by simp⟩
  | append_singleton dirs v ih =>
    intro s
    obtain ⟨t, ht⟩ := ih (D s v)
    refine ⟨t, fun χ u => ?_⟩
    rw [iteratedFDeriv_append_singleton ((hcalc χ).1 s),
      show (fun w => fderiv ℝ (Ψ s χ) w v) = Ψ (D s v) χ from funext fun w => (hcalc χ).2 s w v]
    exact ht χ u

end Charts

section Stages

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

set_option maxHeartbeats 1500000 in
/-- The Fourier integral of a realized Schwartz stage is realized by the
dual elementary Schwartz stage. The mixed derivatives and the weights
are both computed in the actual dual quotient coordinates. -/
theorem BruhatSchwartzStage.exists_fourier_realize (p : BruhatSchwartzStage G)
    (e : ElementaryLCAPresentation p.1.dual.StageQuotient) (s : p.Space) :
    let p' : BruhatSchwartzStage (PontryaginDual G) := ⟨p.1.dual, e⟩
    ∃ t : p'.Space, p'.realize t = lcaFourier μ (p.realize s) := by
  classical
  intro p'
  obtain ⟨d, hd⟩ := p.1.dualStagePairing
  let H := p.1.upper.val
  let E := ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
  let Y := ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor
  let V := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let q (x : H) : E := (p.1.stageCoordinates p.2 x).toAdd
  let ν := μ.comap H.subtype
  let re : Multiplicative E →ₜ* p.1.StageQuotient :=
    ⟨p.2.equiv.symm.toMulEquiv.toMonoidHom, p.2.equiv.symm.continuous⟩
  let de : Multiplicative Y →ₜ* p.1.dual.StageQuotient :=
    ⟨e.equiv.symm.toMulEquiv.toMonoidHom, e.equiv.symm.continuous⟩
  let η : Multiplicative Y →ₜ* PontryaginDual (Multiplicative E) :=
    (PontryaginDual.map re).comp (d.comp de)
  let cover : Multiplicative V →ₜ* Multiplicative Y :=
    ⟨elementaryCoverHom.toMultiplicative, elementaryCoverHom_continuous⟩
  let α := η.comp cover
  let base (a : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :=
    η (Multiplicative.ofAdd (elementaryCover (0 : V) a b))
  let F (f : p.Space) (y : Y) :=
    ∫ x : H, f (q x) * star (η (Multiplicative.ofAdd y) (Multiplicative.ofAdd (q x)) : ℂ) ∂ν
  let coord (χ : p.1.dual.upper.val) : Y := (p.1.dual.stageCoordinates e χ).toAdd
  have hf (f : p.Space) (χ : p.1.dual.upper.val) :
      F f (coord χ) = lcaFourier μ (p.realize f) χ.val := by
    rw [p.fourier_quotientIntegral μ f d hd χ]
    apply integral_congr_ae
    exact .of_forall fun x => by
      change f (q x) * star (d (e.equiv.symm (e.equiv (QuotientGroup.mk χ)))
        (p.2.equiv.symm (p.2.equiv (QuotientGroup.mk x))) : ℂ) = _
      rw [e.equiv.symm_apply_apply, p.2.equiv.symm_apply_apply]
  have hq : Continuous q := (p.1.stageCoordinates p.2).continuous
  have hi (f : p.Space) : Integrable (fun x : H => f (q x)) ν := by
    have h := (integrableOn_iff_comap_subtypeVal p.1.upper.property.1.measurableSet).mp
      (p.integrable μ f).integrableOn
    exact h.congr (.of_forall fun x => p.1.realizeSchwartz_apply_of_mem p.2 f x)
  have hm (ψ : PontryaginDual (Multiplicative E)) :
      AEStronglyMeasurable (fun x : H => (ψ (Multiplicative.ofAdd (q x)) : ℂ)) ν :=
    (continuous_subtype_val.comp (ψ.continuous.comp (continuous_ofAdd.comp hq))).aestronglyMeasurable
  obtain ⟨hSmooth, hDeriv⟩ := elementaryFourier_charts ν q α hi hm
  let Ψ (f : p.Space) (χ : PontryaginDual (Multiplicative E)) (u : V) :=
    ∫ x : H, f (q x) * star ((χ * α (Multiplicative.ofAdd u)) (Multiplicative.ofAdd (q x)) : ℂ) ∂ν
  have hCover (f : p.Space) (a : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
      (fun u : V => F f (elementaryCover u a b)) = Ψ f (base a b) := by
    funext u
    have he : elementaryCover u a b = elementaryCover (0 : V) a b + elementaryCoverHom u := by
      simpa only [zero_add] using elementaryCover_add (0 : V) u a b
    change (∫ x : H, f (q x) * star (η (Multiplicative.ofAdd (elementaryCover u a b))
      (Multiplicative.ofAdd (q x)) : ℂ) ∂ν) = _
    rw [he, ofAdd_add, map_mul]
    rfl
  have hsurj : Surjective coord := by
    intro y
    obtain ⟨χ, hχ⟩ := QuotientGroup.mk'_surjective
      (p.1.dual.kernel.comap p.1.dual.upper.val.subtype) (e.equiv.symm (Multiplicative.ofAdd y))
    refine ⟨χ, ?_⟩
    change (e.equiv (QuotientGroup.mk χ)).toAdd = y
    change QuotientGroup.mk χ = e.equiv.symm (Multiplicative.ofAdd y) at hχ
    rw [hχ, e.equiv.apply_symm_apply]
    rfl
  have hbound (f : p.Space) (P : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ) :
      ∃ C : ℝ, ∀ y : Y, ‖MvPolynomial.eval (elementaryGrowthVariables y) P * F f y‖ ≤ C := by
    obtain ⟨C, hC⟩ := p.fourier_polynomial_bound μ e f P
    refine ⟨C, fun y => ?_⟩
    obtain ⟨χ, rfl⟩ := hsurj y
    rw [hf]
    exact hC χ
  have hmem : F s ∈ elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := by
    refine ⟨fun a b => hCover s a b ▸ hSmooth s (base a b), fun i => ?_⟩
    let dirs : List V := (List.ofFn fun j => List.replicate (i.2.1 j) (EuclideanSpace.single j 1, 0)).flatten ++
      (List.ofFn fun j => List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1)).flatten
    obtain ⟨t, ht⟩ := hDeriv dirs s
    let P : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ :=
      (∏ j, MvPolynomial.X (Sum.inl j) ^ i.1 j) *
        ∏ j, MvPolynomial.X (Sum.inr j) ^ i.2.2.2 j
    obtain ⟨C, hC⟩ := hbound t P
    apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    refine iSup_le fun u => iSup_le fun a => iSup_le fun b => ?_
    let W : ℂ := (∏ j, (u.1 j : ℂ) ^ i.1 j) * ∏ j, (a j : ℂ) ^ i.2.2.2 j
    change ‖W * elementaryPartial (F s) i.2.1 i.2.2.1 u a b‖ₑ ≤ _
    have hp : elementaryPartial (F s) i.2.1 i.2.2.1 u a b = F t (elementaryCover u a b) := by
      change iteratedFDeriv ℝ dirs.length (fun w => F s (elementaryCover w a b)) u dirs.get = _
      rw [hCover s a b]
      exact (ht (base a b) u).trans (congrFun (hCover t a b) u).symm
    rw [hp, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa [P, W, elementaryGrowthVariables, elementaryCover] using hC (elementaryCover u a b)
  let t : p'.Space := ⟨F s, hmem⟩
  refine ⟨t, funext fun χ => ?_⟩
  change p.1.dual.realizeSchwartz e t χ = _
  by_cases hχ : χ ∈ p.1.dual.upper.val
  · exact (p.1.dual.realizeSchwartz_apply_of_mem e t ⟨χ, hχ⟩).trans (hf s ⟨χ, hχ⟩)
  · rw [p.1.dual.realizeSchwartz_apply_of_not_mem e t χ hχ]
    exact (notMem_support.mp (fun h => hχ ((p.fourier_support_invariant μ s).1 h))).symm

end Stages
end
end Masullo
