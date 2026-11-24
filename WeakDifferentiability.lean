import PettisBounds
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import WeakBoundedness
import PartialDifferentiation

open Filter Function Set Topology

namespace Masullo

section WeakDifferential

variable {𝕜 V E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedSpace 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [Module 𝕜 (WeakAlgebraicBidual E)] [IsScalarTower 𝕜 ℂ (WeakAlgebraicBidual E)]

private noncomputable abbrev bidualIdentity :
    Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ] Module.Dual ℂ (StrongDual ℂ E) := LinearMap.id

private noncomputable def bidualEvaluations :
    WeakAlgebraicBidual E →L[𝕜] (StrongDual ℂ E → ℂ) :=
  let j : WeakAlgebraicBidual E →L[ℂ] (StrongDual ℂ E → ℂ) :=
    { toFun := fun m ℓ => bidualIdentity m ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := WeakBilin.coeFn_continuous bidualIdentity }
  j.restrictScalars 𝕜

private theorem bidualEvaluations_apply (b : WeakAlgebraicBidual E) (ℓ : StrongDual ℂ E) :
    bidualEvaluations (𝕜 := 𝕜) b ℓ = bidualIdentity b ℓ := rfl

private theorem bidualEvaluations_isEmbedding :
    IsEmbedding (bidualEvaluations (E := E) (𝕜 := 𝕜)) :=
  WeakBilin.isEmbedding (B := bidualIdentity) injective_id

private theorem bidualEval_fderiv_iff {f : V → E} {A : V →L[𝕜] WeakAlgebraicBidual E} {x : V} :
    HasFDerivAt (fun y => weakBidualEval E (f y)) A x ↔
    ∀ ℓ : StrongDual ℂ E, HasFDerivAt (fun y => ℓ (f y))
      ((ContinuousLinearMap.proj ℓ).comp ((bidualEvaluations (𝕜 := 𝕜)).comp A)) x := by
  let e := bidualEvaluations (E := E) (𝕜 := 𝕜)
  let F := fun y => weakBidualEval E (f y)
  have he : IsEmbedding e := bidualEvaluations_isEmbedding
  change HasFDerivAt F A x ↔ ∀ ℓ, HasFDerivAt (fun y => (e ∘ F) y ℓ)
    ((ContinuousLinearMap.proj ℓ).comp (e.comp A)) x
  rw [← hasFDerivAt_pi']
  let r := fun y => F y - F x - A (y - x)
  have hr (y : V) : (e ∘ r) y = (e ∘ F) y - (e ∘ F) x - (e.comp A) (y - x) := by
    simp [r]
  constructor
  · intro h
    apply HasFDerivAt.of_isLittleOTVS
    exact (e.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS).congr_left hr
  · intro h
    apply HasFDerivAt.of_isLittleOTVS
    exact (e.isThetaTVS_comp he.isInducing).symm.trans_isLittleOTVS
      (h.isLittleOTVS.congr_left fun y => (hr y).symm)

private theorem bidualEval_directional {f : V → E} {A : V →L[𝕜] WeakAlgebraicBidual E}
    {x : V} (h : HasFDerivAt (fun y => weakBidualEval E (f y)) A x) (v : V) :
    Tendsto (fun t : 𝕜 => t⁻¹ • (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x)))
      (𝓝[≠] 0) (𝓝 (A v)) := by
  let q : 𝕜 →L[𝕜] V := ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) v
  have hq : HasFDerivAt (fun t : 𝕜 => x + t • v) q 0 := q.hasFDerivAt.const_add x
  apply (bidualEvaluations_isEmbedding (𝕜 := 𝕜)).tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro ℓ
  let e := (ContinuousLinearMap.proj ℓ).comp (bidualEvaluations (E := E) (𝕜 := 𝕜))
  have hℓ := bidualEval_fderiv_iff.mp h ℓ
  have hℓ' : HasFDerivAt (fun y => ℓ (f y)) (e.comp A) (x + (0 : 𝕜) • v) := by
    rw [zero_smul, add_zero]
    simpa [e, ContinuousLinearMap.comp_assoc] using hℓ
  have hline := (hℓ'.comp (0 : 𝕜) hq).hasDerivAt
  have hs : Tendsto (fun t : 𝕜 => t⁻¹ • (ℓ (f (x + t • v)) - ℓ (f x))) (𝓝[≠] 0)
      (𝓝 (e (A v))) := by
    simpa [Function.comp_def, q] using hline.tendsto_slope_zero
  change Tendsto (fun t : 𝕜 => e (t⁻¹ • (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x))))
    (𝓝[≠] 0) (𝓝 (e (A v)))
  have heval (y : E) : e (weakBidualEval E y) = ℓ y := rfl
  simp only [map_smul, map_sub, heval]
  exact hs

/-- Lemma C.5.1.12. The weak differential is continuous exactly when the
same differential defines continuous Fréchet differentiability in the
weak algebraic bidual. The directional difference quotients have that
differential as their limit. -/
theorem weakContinuousDifferentiability_iff {U : Set V} (f : V → E)
    (A : V → V →L[𝕜] WeakAlgebraicBidual E) :
    ((∀ ℓ : StrongDual ℂ E, ∀ x ∈ U, HasFDerivAt (fun y => ℓ (f y))
        ((ContinuousLinearMap.proj ℓ).comp ((bidualEvaluations (𝕜 := 𝕜)).comp (A x))) x) ∧
      ContinuousOn (fun p : V × V => A p.1 p.2) (U ×ˢ univ)) ↔
    ((∀ x ∈ U, HasFDerivAt (fun y => weakBidualEval E (f y)) (A x) x) ∧
      ContinuousOn (fun p : V × V => A p.1 p.2) (U ×ˢ univ) ∧
      ∀ x ∈ U, ∀ v,
        Tendsto (fun t : 𝕜 => t⁻¹ • (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x)))
          (𝓝[≠] 0) (𝓝 (A x v))) := by
  constructor
  · intro ⟨hs, hc⟩
    have hf x (hx : x ∈ U) := bidualEval_fderiv_iff.mpr fun ℓ => hs ℓ x hx
    exact ⟨hf, hc, fun x hx v => bidualEval_directional (hf x hx) v⟩
  · rintro ⟨hf, hc, _⟩
    exact ⟨fun ℓ x hx => bidualEval_fderiv_iff.mp (hf x hx) ℓ, hc⟩

/-- Assemble the one-dimensional weak differential from a continuous scalar
derivative family. Linearity in the scalar test follows from uniqueness. -/
theorem continuousWeakDifferential_of_scalar_continuousDerivatives
    [SMulCommClass ℂ 𝕜 ℂ] {U : Set 𝕜} (f : 𝕜 → E)
    (d : StrongDual ℂ E → 𝕜 → ℂ)
    (hd : ∀ ℓ, ∀ x ∈ U, HasDerivAt (fun y => ℓ (f y)) (d ℓ x) x)
    (hc : ∀ ℓ, ContinuousOn (d ℓ) U) :
    ∃ B : 𝕜 → 𝕜 →L[𝕜] WeakAlgebraicBidual E,
      (∀ x ∈ U, HasFDerivAt (fun y => weakBidualEval E (f y)) (B x) x) ∧
      ContinuousOn (fun p : 𝕜 × 𝕜 => B p.1 p.2) (U ×ˢ univ) := by
  classical
  let D (x : 𝕜) (hx : x ∈ U) : WeakAlgebraicBidual E :=
    (show Module.Dual ℂ (StrongDual ℂ E) from
      { toFun := fun ℓ => d ℓ x
        map_add' := by
          intro L M
          have hg : HasDerivAt (fun y => (L + M) (f y)) (d L x + d M x) x :=
            (hd L x hx).add (hd M x hx)
          exact (hd (L + M) x hx).unique hg
        map_smul' := by
          intro c L
          have hg : HasDerivAt (fun y => (c • L) (f y)) (c • d L x) x :=
            (hd L x hx).const_smul c
          exact (hd (c • L) x hx).unique hg })
  let j : 𝕜 →L[𝕜] ℂ := (ContinuousLinearMap.id 𝕜 𝕜).smulRight 1
  let B (x : 𝕜) : 𝕜 →L[𝕜] WeakAlgebraicBidual E :=
    if hx : x ∈ U then
      (((ContinuousLinearMap.id ℂ ℂ).smulRight (D x hx)).restrictScalars 𝕜).comp j
    else 0
  have hB (x : 𝕜) (hx : x ∈ U) (v : 𝕜) (ℓ : StrongDual ℂ E) :
      bidualIdentity (B x v) ℓ = v • d ℓ x := by
    have hb : B x v = (v • (1 : ℂ)) • D x hx := by
      dsimp only [B]
      rw [dite_eq_left hx]
      rfl
    rw [hb]
    change (v • (1 : ℂ)) • d ℓ x = v • d ℓ x
    simpa only [one_smul] using smul_assoc v (1 : ℂ) (d ℓ x)
  refine ⟨B, fun x hx => bidualEval_fderiv_iff.mpr (fun ℓ => ?_), ?_⟩
  · have he : (ContinuousLinearMap.proj ℓ).comp ((bidualEvaluations (𝕜 := 𝕜)).comp (B x)) =
        (ContinuousLinearMap.id 𝕜 𝕜).smulRight (d ℓ x) := by
      apply DFunLike.ext
      intro v
      exact hB x hx v ℓ
    rw [he]
    exact (hd ℓ x hx).hasFDerivAt
  · rw [continuousOn_iff_continuous_domRestrict]
    apply WeakBilin.continuous_of_continuous_eval bidualIdentity
    intro ℓ
    have hE : (fun p : (U ×ˢ (univ : Set 𝕜)) => bidualIdentity (B p.1.1 p.1.2) ℓ) =
        fun p : (U ×ˢ (univ : Set 𝕜)) => p.1.2 • d ℓ p.1.1 := by
      funext p
      exact hB p.1.1 p.2.1 p.1.2 ℓ
    change Continuous (fun p : (U ×ˢ (univ : Set 𝕜)) => bidualIdentity (B p.1.1 p.1.2) ℓ)
    rw [hE]
    have hp : ContinuousOn (fun p : 𝕜 × 𝕜 => p.2 • d ℓ p.1) (U ×ˢ (univ : Set 𝕜)) :=
      continuous_snd.continuousOn.smul ((hc ℓ).comp continuous_fst.continuousOn (fun _ hx => hx.1))
    exact continuousOn_iff_continuous_domRestrict.mp hp


section Coordinates

variable [IsRCLikeNormedField 𝕜] {n : ℕ}

private theorem continuousOn_bidual_iff {X : Type*} [TopologicalSpace X] {S : Set X}
    {A : X → WeakAlgebraicBidual E} :
    ContinuousOn A S ↔ ∀ ℓ : StrongDual ℂ E, ContinuousOn (fun x => bidualIdentity (A x) ℓ) S := by
  simp only [continuousOn_iff_continuous_domRestrict]
  constructor
  · intro h ℓ
    exact (WeakBilin.eval_continuous bidualIdentity ℓ).comp h
  · intro h
    exact WeakBilin.continuous_of_continuous_eval bidualIdentity h

/-- Assemble a weak differential from its finitely many coordinate values. -/
private noncomputable def weakCoordinateDifferential (d : Fin n → WeakAlgebraicBidual E) :
    (Fin n → 𝕜) →L[𝕜] WeakAlgebraicBidual E where
  toFun v := ∑ i, v i • d i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [smul_smul, Finset.smul_sum]
  cont := WeakBilin.continuous_of_continuous_eval bidualIdentity fun ℓ => by
    let e := (ContinuousLinearMap.proj ℓ).comp (bidualEvaluations (E := E) (𝕜 := 𝕜))
    change Continuous (fun v : Fin n → 𝕜 => e (∑ i, v i • d i))
    simp only [map_sum, map_smul]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

omit [IsRCLikeNormedField 𝕜] in
private theorem coordinateWeakDifferential_apply (d : Fin n → WeakAlgebraicBidual E)
    (v : Fin n → 𝕜) :
    weakCoordinateDifferential d v = ∑ i, v i • d i := rfl

omit [IsRCLikeNormedField 𝕜] in
private theorem weakCoordinateDifferential_continuousOn {U : Set (Fin n → 𝕜)}
    (d : Fin n → (Fin n → 𝕜) → WeakAlgebraicBidual E)
    (hd : ∀ i, ContinuousOn (d i) U) :
    ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) =>
      weakCoordinateDifferential (fun i => d i p.1) p.2) (U ×ˢ univ) := by
  apply continuousOn_bidual_iff.mpr
  intro ℓ
  let e := (ContinuousLinearMap.proj ℓ).comp (bidualEvaluations (E := E) (𝕜 := 𝕜))
  change ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) =>
    e (weakCoordinateDifferential (fun i => d i p.1) p.2)) _
  simp only [coordinateWeakDifferential_apply, map_sum, map_smul]
  apply continuousOn_finsetSum
  intro i hi
  have hc₁ : Continuous (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hc₂ : ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => e (d i p.1)) (U ×ˢ univ) :=
    e.continuous.comp_continuousOn ((hd i).comp continuous_fst.continuousOn (fun _ hp => hp.1))
  exact hc₁.continuousOn.smul hc₂

omit [IsRCLikeNormedField 𝕜] in
private theorem hasDerivAt_of_directional_bidual_limit
    {f : (Fin n → 𝕜) → E} {x v : Fin n → 𝕜} {B : WeakAlgebraicBidual E}
    (h : Tendsto (fun t : 𝕜 => t⁻¹ •
      (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x))) (𝓝[≠] 0) (𝓝 B))
    (ℓ : StrongDual ℂ E) : HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • v))) (bidualIdentity B ℓ) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  let e := (ContinuousLinearMap.proj ℓ).comp (bidualEvaluations (E := E) (𝕜 := 𝕜))
  have hL := e.continuous.continuousAt.tendsto.comp h
  have heval (y : E) : e (weakBidualEval E y) = ℓ y := rfl
  simp only [zero_add, zero_smul, add_zero]
  change Tendsto (fun t : 𝕜 => e (t⁻¹ • (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x))))
    (𝓝[≠] 0) (𝓝 (e B)) at hL
  have hB : e B = bidualIdentity B ℓ := rfl
  simpa only [map_smul, map_sub, heval, hB] using hL

private theorem weakCoordinateDifferential_hasFDerivAt {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E) (d : Fin n → (Fin n → 𝕜) → WeakAlgebraicBidual E)
    (hd : ∀ i, ContinuousOn (d i) U)
    (hp : ∀ i, ∀ x ∈ U, ∀ ℓ : StrongDual ℂ E,
      HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (bidualIdentity (d i x) ℓ) 0)
    {x : Fin n → 𝕜} (hx : x ∈ U) :
    HasFDerivAt (fun y => weakBidualEval E (f y)) (weakCoordinateDifferential fun i => d i x) x := by
  apply bidualEval_fderiv_iff.mpr
  intro ℓ
  let e := (ContinuousLinearMap.proj ℓ).comp (bidualEvaluations (E := E) (𝕜 := 𝕜))
  let H (i : Fin n) (y : Fin n → 𝕜) := e (d i y)
  have hH : ∀ i, ContinuousOn (H i) U := fun i => e.continuous.comp_continuousOn (hd i)
  have hD := hasFDerivAt_of_continuous_coordinate_derivatives hU (fun y => ℓ (f y))
    H (fun i y hy => hp i y hy ℓ) hH hx
  have he : (ContinuousLinearMap.proj ℓ).comp
      ((bidualEvaluations (𝕜 := 𝕜)).comp (weakCoordinateDifferential fun i => d i x)) =
      coordinateDifferential (𝕜 := 𝕜) (fun i => H i x) := by
    ext v
    change e (weakCoordinateDifferential (𝕜 := 𝕜) (fun i => d i x) v) = _
    simp [coordinateDifferential_apply, coordinateWeakDifferential_apply, H]
  rw [he]
  exact hD

/-- Lemma C.5.1.15. Weak continuous differentiability is equivalent to
continuous weak coordinate derivatives on an open coordinate domain. -/
theorem weakContinuousDifferentiability_iff_coordinate {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E) :
    (∃ B : (Fin n → 𝕜) → (Fin n → 𝕜) →L[𝕜] WeakAlgebraicBidual E,
      (∀ x ∈ U, HasFDerivAt (fun y => weakBidualEval E (f y)) (B x) x) ∧
      ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => B p.1 p.2) (U ×ˢ univ)) ↔
    (∃ d : Fin n → (Fin n → 𝕜) → WeakAlgebraicBidual E, (∀ i, ContinuousOn (d i) U) ∧
      ∀ i, ∀ x ∈ U, ∀ ℓ : StrongDual ℂ E,
        HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (bidualIdentity (d i x) ℓ) 0) := by
  constructor
  · rintro ⟨B, hB, hc⟩
    refine ⟨fun i x => B x (Pi.single i 1), fun i => ?_, fun i x hx ℓ => ?_⟩
    · exact hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, mem_univ _⟩)
    · exact hasDerivAt_of_directional_bidual_limit (bidualEval_directional (hB x hx) _) ℓ
  · rintro ⟨d, hd, hp⟩
    exact ⟨fun x => weakCoordinateDifferential (fun i => d i x),
      fun _ hx => weakCoordinateDifferential_hasFDerivAt hU f d hd hp hx,
      weakCoordinateDifferential_continuousOn d hd⟩

/-- The first two clauses of C.5.1.16. Weak Gâteaux limits give scalar
coordinate derivatives, and a jointly continuous limit is the weak differential. -/
theorem weakGateaux_coordinate_and_differential {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E) (G : (Fin n → 𝕜) → (Fin n → 𝕜) → WeakAlgebraicBidual E)
    (hG : ∀ x ∈ U, ∀ v, Tendsto (fun t : 𝕜 => t⁻¹ •
      (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x))) (𝓝[≠] 0) (𝓝 (G x v))) :
    (∀ i, ∀ x ∈ U, ∀ ℓ : StrongDual ℂ E, HasDerivAt
      (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (bidualIdentity (G x (Pi.single i 1)) ℓ) 0) ∧
    (ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => G p.1 p.2) (U ×ˢ univ) →
      ∃ B : (Fin n → 𝕜) → (Fin n → 𝕜) →L[𝕜] WeakAlgebraicBidual E,
        (∀ x ∈ U, HasFDerivAt (fun y => weakBidualEval E (f y)) (B x) x) ∧
        ∀ x ∈ U, ∀ v, B x v = G x v) := by
  have hp (i : Fin n) (x : Fin n → 𝕜) (hx : x ∈ U) (ℓ : StrongDual ℂ E) :=
    hasDerivAt_of_directional_bidual_limit (hG x hx (Pi.single i 1)) ℓ
  refine ⟨hp, fun hc => ?_⟩
  let d (i : Fin n) (x : Fin n → 𝕜) := G x (Pi.single i 1)
  have hd (i : Fin n) : ContinuousOn (d i) U :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, mem_univ _⟩)
  let B (x : Fin n → 𝕜) := weakCoordinateDifferential (𝕜 := 𝕜) (fun i => d i x)
  have hB (x : Fin n → 𝕜) (hx : x ∈ U) : HasFDerivAt (fun y => weakBidualEval E (f y)) (B x) x :=
    weakCoordinateDifferential_hasFDerivAt hU f d hd hp hx
  letI : T2Space (WeakAlgebraicBidual E) := (bidualEvaluations_isEmbedding (𝕜 := 𝕜)).t2Space
  exact ⟨B, hB, fun x hx v => tendsto_nhds_unique
    (bidualEval_directional (hB x hx) v) (hG x hx v)⟩

end Coordinates

end WeakDifferential


section BoundedRatios

open Bornology

variable {𝕜 V E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedSpace 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [PolynormableSpace ℂ E]

omit [IsScalarTower 𝕜 ℂ ℂ] in
/-- Corrected C.5.1.13(1). The ratios are bounded on every compact
convex set on which the weak differential is continuous. -/
theorem weakDifferential_bounded_ratios {K : Set V} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : V → E) (D : StrongDual ℂ E → V → V →L[𝕜] ℂ)
    (hD : ∀ ℓ : StrongDual ℂ E, ∀ x ∈ K, HasFDerivAt (fun y => ℓ (f y)) (D ℓ x) x)
    (hc : ∀ ℓ, ContinuousOn (fun p : V × V => D ℓ p.1 p.2) (K ×ˢ univ)) :
    IsVonNBounded ℂ {z : E | ∃ x ∈ K, ∃ y ∈ K, z = ‖y - x‖⁻¹ • (f y - f x)} := by
  apply (isVonNBounded_iff_dual_images _).mpr
  intro ℓ
  have hcompact := hK.prod (isCompact_closedBall (0 : V) 1)
  have himage : IsCompact ((fun p : V × V => D ℓ p.1 p.2) '' (K ×ˢ Metric.closedBall 0 1)) :=
    hcompact.image_of_continuousOn ((hc ℓ).mono (prod_mono_right (subset_univ _)))
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp himage.isBounded
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hnorm (x : V) (hx : x ∈ K) : ‖D ℓ x‖ ≤ C := by
    letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
    intro v hv
    have hmem : v ∈ Metric.closedBall (0 : V) 1 := by simp [Metric.mem_closedBall, dist_zero_right, hv]
    apply (hM _ (mem_image_of_mem _ (show (x,v) ∈ K ×ˢ Metric.closedBall 0 1 from ⟨hx,hmem⟩))).trans
    exact le_max_left _ _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  rintro z ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hdiff : ‖ℓ (f y) - ℓ (f x)‖ ≤ C * ‖y - x‖ :=
    hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun v hv => (hD ℓ v hv).hasFDerivWithinAt) hnorm hx hy
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub, norm_smul,
    RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
  by_cases he : y - x = 0
  · simpa [he] using hC
  · exact (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans_eq (by
      rw [mul_comm C, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr he), one_mul])

omit [IsScalarTower 𝕜 ℂ ℂ] in
theorem continuousOn_of_continuous_weakDifferential {U : Set V} (hU : IsOpen U)
    (f : V → E) (D : StrongDual ℂ E → V → V →L[𝕜] ℂ)
    (hD : ∀ ℓ : StrongDual ℂ E, ∀ x ∈ U, HasFDerivAt (fun y => ℓ (f y)) (D ℓ x) x)
    (hc : ∀ ℓ, ContinuousOn (fun p : V × V => D ℓ p.1 p.2) (U ×ˢ univ)) :
    ContinuousOn f U := by
  intro x hx
  obtain ⟨r, hr, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let K := Metric.closedBall x r
  have hR := weakDifferential_bounded_ratios (isCompact_closedBall x r) (convex_closedBall x r)
    f D (fun ℓ y hy => hD ℓ y (hK hy)) (fun ℓ => (hc ℓ).mono (prod_mono_left hK))
  let hp := PolynormableSpace.withSeminorms ℂ E
  have hC : ContinuousAt f x := by
    apply (hp.tendsto_nhds f (f x)).mpr
    intro p ε hε
    obtain ⟨M, hM, hBp⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hR p
    have hrad : 0 < min r (ε / M) := lt_min hr (div_pos hε hM)
    filter_upwards [Metric.ball_mem_nhds x hrad] with y hy
    have hd : ‖y - x‖ < min r (ε / M) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hyK : y ∈ K := by
      simpa only [K, Metric.mem_closedBall, dist_eq_norm] using (hd.trans_le (min_le_left _ _)).le
    by_cases h : y = x
    · simp [h, hε]
    have hn : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
    have hB := hBp _ ⟨x, Metric.mem_closedBall_self hr.le, y, hyK, rfl⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul_eq_mul, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity)] at hB
    have hlo : p.1 (f y - f x) < M * (ε / M) := by
      have hm := mul_le_mul_of_nonneg_left hB.le (norm_nonneg (y - x))
      rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_comm ‖y - x‖] at hm
      exact hm.trans_lt (mul_lt_mul_of_pos_left (hd.trans_le (min_le_right _ _)) hM)
    simpa [mul_div_cancel₀ _ hM.ne'] using hlo
  exact hC.continuousWithinAt

theorem quadratic_weakly_smooth :
    ∀ ℓ : StrongDual ℂ ℂ, ContDiff ℝ 1 (fun x : ℝ => ℓ ((x : ℂ) ^ 2)) := by
  intro ℓ
  have hℓ : ContDiff ℝ 1 (ℓ.restrictScalars ℝ : ℂ →L[ℝ] ℂ) :=
    (ℓ.restrictScalars ℝ).contDiff
  exact hℓ.comp (Complex.ofRealCLM.contDiff.pow 2)

/-- The original global bound in C.5.1.13(1) already fails for a smooth
scalar function on the whole real line. -/
theorem quadratic_bounded_ratios_obstruction :
    ¬IsBounded {z : ℂ | ∃ x y : ℝ, 0 < |y - x| ∧ |y - x| ≤ 1 ∧
      z = |y - x|⁻¹ • (((y : ℂ) ^ 2) - (x : ℂ) ^ 2)} := by
  intro h
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp h
  let x : ℝ := max M 0 + 1
  let y : ℝ := x + 1
  have hyx : y - x = 1 := by dsimp [y]; ring
  have hmem : ((2 * x + 1 : ℝ) : ℂ) ∈ {z : ℂ | ∃ x y : ℝ,
      0 < |y - x| ∧ |y - x| ≤ 1 ∧ z = |y - x|⁻¹ • ((y : ℂ) ^ 2 - (x : ℂ) ^ 2)} := by
    refine ⟨x, y, by simp [hyx], by simp [hyx], ?_⟩
    simp only [hyx, abs_one, inv_one, one_smul]
    push_cast
    dsimp [y]
    push_cast
    ring
  have hv := hM _ hmem
  have hx : 0 ≤ x := by dsimp [x]; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hv
  dsimp [x] at hv
  linarith [le_max_left M (0 : ℝ), le_max_right M (0 : ℝ)]

end BoundedRatios


section StrongDirectional

variable {𝕜 V E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedSpace 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [AddCommGroup E] [Module ℂ E] [Module 𝕜 E] [IsScalarTower 𝕜 ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [PolynormableSpace ℂ E]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- C.5.1.13(2). If the weak differential is continuously E-valued,
the directional difference quotients converge in the original topology. -/
theorem strong_directional_of_continuous_weakDifferential {U : Set V} (hU : IsOpen U)
    (f : V → E) (A : V → V →L[𝕜] E)
    (hA : ContinuousOn (fun p : V × V => A p.1 p.2) (U ×ˢ univ))
    (hD : ∀ ℓ : StrongDual ℂ E, ∀ x ∈ U,
      HasFDerivAt (fun y => ℓ (f y)) ((ℓ.restrictScalars 𝕜).comp (A x)) x)
    {x : V} (hx : x ∈ U) (v : V) :
    Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + t • v) - f x)) (𝓝[≠] 0) (𝓝 (A x v)) := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let q : 𝕜 →L[𝕜] V := ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) v
  let γ (t : 𝕜) := x + t • v
  have hγ (t : 𝕜) : HasFDerivAt γ q t := q.hasFDerivAt.const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have hγc : ContinuousAt γ 0 := (hγ 0).continuousAt
  have hAc : ContinuousAt (fun z => A z v) x := by
    let G : V × V → E := fun p => A p.1 p.2
    let j : V → V × V := fun z => (z, v)
    have ha : ContinuousAt G (j x) := hA.continuousAt
      ((hU.prod isOpen_univ).mem_nhds (show (x, v) ∈ U ×ˢ univ from ⟨hx, mem_univ v⟩))
    have hk : ContinuousAt j x := continuousAt_id.prodMk continuousAt_const
    change ContinuousAt (G ∘ j) x
    exact ha.comp hk
  let hp := PolynormableSpace.withSeminorms ℂ E
  apply (hp.tendsto_nhds _ _).mpr
  intro p ε hε
  have hE : ContinuousAt (fun t => p.1 (A (γ t) v - A x v)) 0 :=
    p.2.continuousAt.comp ((hAc.comp_of_eq hγc hγ0).sub continuousAt_const)
  have hbelow : ∀ᶠ t in 𝓝 (0 : 𝕜), γ t ∈ U ∧ p.1 (A (γ t) v - A x v) < ε / 2 := by
    have hγU := hγc.tendsto.eventually_mem (hγ0 ▸ hU.mem_nhds hx)
    have hsmall : p.1 (A (γ 0) v - A x v) < ε / 2 := by simpa [hγ0] using half_pos hε
    exact hγU.and (hE.tendsto.eventually_mem (Iio_mem_nhds hsmall))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hbelow
  have hev : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), t ∈ Metric.ball (0 : 𝕜) (r / 2) ∧ t ≠ 0 := by
    have hb : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), t ∈ Metric.ball (0 : 𝕜) (r / 2) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (half_pos hr))
    exact hb.and self_mem_nhdsWithin
  filter_upwards [hev] with t ht
  refine (seminorm_le_of_dual_unit_bounds p _ (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  intro ℓ hℓ
  let L := ℓ.restrictScalars 𝕜
  let g (t : 𝕜) := ℓ (f (γ t)) - t • ℓ (A x v)
  let K := Metric.closedBall (0 : 𝕜) (r / 2)
  have hK : K ⊆ Metric.ball (0 : 𝕜) r := Metric.closedBall_subset_ball (half_lt_self hr)
  have h0 : (0 : 𝕜) ∈ K := Metric.mem_closedBall_self (half_pos hr).le
  have htK : t ∈ K := Metric.ball_subset_closedBall ht.1
  have hg (u : 𝕜) (hu : u ∈ K) : HasDerivWithinAt g (ℓ (A (γ u) v - A x v)) K u := by
    have h₁ : HasDerivAt (fun w => ℓ (f (γ w))) (ℓ (A (γ u) v)) u := by
      have h := ((hD ℓ (γ u) (hball (hK hu)).1).comp u (hγ u)).hasDerivAt
      simpa [q, Function.comp_def] using h
    have h₂ : HasDerivAt (fun w : 𝕜 => w • ℓ (A x v)) (ℓ (A x v)) u :=
      by
        let S := ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) (ℓ (A x v))
        have hS : HasFDerivAt (fun w => w • ℓ (A x v)) S u := S.hasFDerivAt
        have hS₁ : S 1 = ℓ (A x v) := by simp [S]
        simpa only [hS₁] using hS.hasDerivAt
    have hh : ℓ (A (γ u) v - A x v) = ℓ (A (γ u) v) - ℓ (A x v) := map_sub _ _ _
    rw [hh]
    exact (h₁.sub h₂).hasDerivWithinAt
  have hnorm (u : 𝕜) (hu : u ∈ K) : ‖ℓ (A (γ u) v - A x v)‖ ≤ ε / 2 :=
    (hℓ _).trans (hball (hK hu)).2.le
  have hgdiff := (convex_closedBall (0 : 𝕜) (r / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg hnorm h0 htK
  have heq : ℓ (t⁻¹ • (f (x + t • v) - f x) - A x v) = t⁻¹ • (g t - g 0) := by
    change L (_ - _) = _
    rw [map_sub, map_smul, map_sub]
    dsimp only [g]
    rw [hγ0, zero_smul, sub_zero]
    change t⁻¹ • (ℓ (f (γ t)) - ℓ (f x)) - ℓ (A x v) = _
    rw [sub_right_comm (ℓ (f (γ t)))]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht.2, one_smul]
  rw [heq, norm_smul, norm_inv]
  rw [sub_zero] at hgdiff
  exact (mul_le_mul_of_nonneg_left hgdiff (by positivity)).trans_eq (by
    rw [mul_comm (ε / 2), ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht.2), one_mul])

/-- The E-valued differential also gives the continuous differential in the
weak algebraic bidual required by Definition C.5.1.8. -/
theorem continuousDifferential_of_Evalued_weakDifferential
    [Module 𝕜 (WeakAlgebraicBidual E)] [IsScalarTower 𝕜 ℂ (WeakAlgebraicBidual E)]
    {U : Set V} (hU : IsOpen U) (f : V → E) (A : V → V →L[𝕜] E)
    (hA : ContinuousOn (fun p : V × V => A p.1 p.2) (U ×ˢ univ))
    (hD : ∀ ℓ : StrongDual ℂ E, ∀ x ∈ U,
      HasFDerivAt (fun y => ℓ (f y)) ((ℓ.restrictScalars 𝕜).comp (A x)) x) :
    ∃ B : V → V →L[𝕜] WeakAlgebraicBidual E,
      (∀ x ∈ U, HasFDerivAt (fun y => weakBidualEval E (f y)) (B x) x) ∧
      ContinuousOn (fun p : V × V => B p.1 p.2) (U ×ˢ univ) ∧
      (∀ x v, B x v = weakBidualEval E (A x v)) ∧
      ∀ x ∈ U, ∀ v, Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + t • v) - f x))
        (𝓝[≠] 0) (𝓝 (A x v)) := by
  let e : E →L[ℂ] WeakAlgebraicBidual E := ⟨weakBidualEval E, weakBidualEval_continuous E⟩
  let B := fun x => (e.restrictScalars 𝕜).comp (A x)
  refine ⟨B, ?_, e.continuous.comp_continuousOn hA, fun _ _ => rfl, ?_⟩
  · intro x hx
    apply bidualEval_fderiv_iff.mpr
    intro ℓ
    have heq : (ContinuousLinearMap.proj ℓ).comp ((bidualEvaluations (𝕜 := 𝕜)).comp (B x)) =
        (ℓ.restrictScalars 𝕜).comp (A x) := by
      ext v
      rfl
    rw [heq]
    exact hD ℓ x hx
  · intro x hx v
    exact strong_directional_of_continuous_weakDifferential hU f A hA hD hx v

section StrongCoordinates

variable [ContinuousSMul 𝕜 E] {n : ℕ}

omit [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ] [Module ℂ E]
  [IsScalarTower 𝕜 ℂ E] [PolynormableSpace ℂ E] in
private theorem continuousOn_coordinateDifferential {U : Set (Fin n → 𝕜)}
    (d : Fin n → (Fin n → 𝕜) → E) (hd : ∀ i, ContinuousOn (d i) U) :
    ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) =>
      coordinateDifferential (fun i => d i p.1) p.2) (U ×ˢ univ) := by
  simp only [coordinateDifferential_apply]
  apply continuousOn_finsetSum
  intro i hi
  have hc₁ : Continuous (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact hc₁.continuousOn.smul ((hd i).comp continuous_fst.continuousOn (fun _ hp => hp.1))

omit [PolynormableSpace ℂ E] in
private theorem coordinateDifferential_scalar_hasFDerivAt {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E) (d : Fin n → (Fin n → 𝕜) → E) (hd : ∀ i, ContinuousOn (d i) U)
    (hp : ∀ i, ∀ x ∈ U, ∀ ℓ : StrongDual ℂ E,
      HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (ℓ (d i x)) 0)
    (ℓ : StrongDual ℂ E) {x : Fin n → 𝕜} (hx : x ∈ U) :
    HasFDerivAt (fun y => ℓ (f y))
      ((ℓ.restrictScalars 𝕜).comp (coordinateDifferential fun i => d i x)) x := by
  let e := ℓ.restrictScalars 𝕜
  let H (i : Fin n) (x : Fin n → 𝕜) := e (d i x)
  have hc : ∀ i, ContinuousOn (H i) U := fun i => e.continuous.comp_continuousOn (hd i)
  have hD := hasFDerivAt_of_continuous_coordinate_derivatives hU (fun y => ℓ (f y))
    H (fun i y hy => hp i y hy ℓ) hc hx
  have he : e.comp (coordinateDifferential fun i => d i x) =
      coordinateDifferential (𝕜 := 𝕜) (fun i => H i x) := by
    ext v
    change e (coordinateDifferential (fun i => d i x) v) = _
    simp [coordinateDifferential_apply, H]
  change HasFDerivAt _ (e.comp (coordinateDifferential fun i => d i x)) x
  rw [he]
  exact hD

/-- C.5.1.16(3). It is enough for each E-valued directional derivative
to depend continuously on the base point for that fixed direction. -/
theorem strongDifferential_of_Evalued_Gateaux [T2Space E]
    [Module 𝕜 (WeakAlgebraicBidual E)] [IsScalarTower 𝕜 ℂ (WeakAlgebraicBidual E)]
    {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E) (G : (Fin n → 𝕜) → (Fin n → 𝕜) → E)
    (hG : ∀ x ∈ U, ∀ v, Tendsto (fun t : 𝕜 => t⁻¹ •
      (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x)))
      (𝓝[≠] 0) (𝓝 (weakBidualEval E (G x v))))
    (hc : ∀ v, ContinuousOn (fun x => G x v) U) :
    ∃ A : (Fin n → 𝕜) → (Fin n → 𝕜) →L[𝕜] E,
      ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => A p.1 p.2) (U ×ˢ univ) ∧
      (∀ ℓ : StrongDual ℂ E, ∀ x ∈ U, HasFDerivAt (fun y => ℓ (f y))
        ((ℓ.restrictScalars 𝕜).comp (A x)) x) ∧
      (∀ x ∈ U, ∀ v, A x v = G x v) ∧
      ∀ x ∈ U, ∀ v, Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + t • v) - f x))
        (𝓝[≠] 0) (𝓝 (G x v)) := by
  let d (i : Fin n) (x : Fin n → 𝕜) := G x (Pi.single i 1)
  have hd (i : Fin n) : ContinuousOn (d i) U := hc (Pi.single i 1)
  have hp (i : Fin n) (x : Fin n → 𝕜) (hx : x ∈ U) (ℓ : StrongDual ℂ E) :
      HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (ℓ (d i x)) 0 :=
    hasDerivAt_of_directional_bidual_limit (hG x hx (Pi.single i 1)) ℓ
  let A (x : Fin n → 𝕜) := coordinateDifferential (𝕜 := 𝕜) (fun i => d i x)
  have hA : ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => A p.1 p.2) (U ×ˢ univ) :=
    continuousOn_coordinateDifferential d hd
  have hD (ℓ : StrongDual ℂ E) (x : Fin n → 𝕜) (hx : x ∈ U) :
      HasFDerivAt (fun y => ℓ (f y)) ((ℓ.restrictScalars 𝕜).comp (A x)) x :=
    coordinateDifferential_scalar_hasFDerivAt hU f d hd hp ℓ hx
  obtain ⟨B, hB, _, hBA, hlim⟩ := continuousDifferential_of_Evalued_weakDifferential hU f A hA hD
  have he : Injective (weakBidualEval E) := (weakBidualEval_isEmbedding E).injective
  letI : T2Space (WeakAlgebraicBidual E) := (bidualEvaluations_isEmbedding (𝕜 := 𝕜)).t2Space
  have heq (x : Fin n → 𝕜) (hx : x ∈ U) (v : Fin n → 𝕜) : A x v = G x v := by
    apply he
    rw [← hBA]
    exact tendsto_nhds_unique (bidualEval_directional (hB x hx) v) (hG x hx v)
  exact ⟨A, hA, hD, heq, fun x hx v => heq x hx v ▸ hlim x hx v⟩

variable [Module 𝕜 (WeakAlgebraicBidual E)] [IsScalarTower 𝕜 ℂ (WeakAlgebraicBidual E)]

/-- The manuscript's continuous differentiability in the original topology,
with the differential represented in the weak algebraic bidual. -/
def ContinuousVectorDifferential (f : (Fin n → 𝕜) → E) (U : Set (Fin n → 𝕜)) : Prop :=
  ∃ (A : (Fin n → 𝕜) → (Fin n → 𝕜) →L[𝕜] E)
    (B : (Fin n → 𝕜) → (Fin n → 𝕜) →L[𝕜] WeakAlgebraicBidual E),
    ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => A p.1 p.2) (U ×ˢ univ) ∧
    (∀ x ∈ U, HasFDerivAt (fun y => weakBidualEval E (f y)) (B x) x) ∧
    ∀ x ∈ U, ∀ v, B x v = weakBidualEval E (A x v)

/-- A continuously E-valued weak differential, specified by the scalar tests. -/
def WeakEValuedDifferential (f : (Fin n → 𝕜) → E) (U : Set (Fin n → 𝕜)) : Prop :=
  ∃ A : (Fin n → 𝕜) → (Fin n → 𝕜) →L[𝕜] E,
    ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => A p.1 p.2) (U ×ˢ univ) ∧
    ∀ ℓ : StrongDual ℂ E, ∀ x ∈ U,
      HasFDerivAt (fun y => ℓ (f y)) ((ℓ.restrictScalars 𝕜).comp (A x)) x

/-- Weak coordinate derivatives that take values in E and are continuous there. -/
def EValuedCoordinateDerivatives (f : (Fin n → 𝕜) → E) (U : Set (Fin n → 𝕜)) : Prop :=
  ∃ d : Fin n → (Fin n → 𝕜) → E, (∀ i, ContinuousOn (d i) U) ∧
    ∀ i, ∀ x ∈ U, ∀ ℓ : StrongDual ℂ E,
      HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (ℓ (d i x)) 0

/-- Weak Gâteaux limits with jointly continuous values in E. -/
def EValuedContinuousGateaux (f : (Fin n → 𝕜) → E) (U : Set (Fin n → 𝕜)) : Prop :=
  ∃ G : (Fin n → 𝕜) → (Fin n → 𝕜) → E,
    ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => G p.1 p.2) (U ×ˢ univ) ∧
    ∀ x ∈ U, ∀ v, Tendsto (fun t : 𝕜 => t⁻¹ •
      (weakBidualEval E (f (x + t • v)) - weakBidualEval E (f x)))
      (𝓝[≠] 0) (𝓝 (weakBidualEval E (G x v)))

/-- The four equivalent conditions for strong vector-valued differentiability
in Theorem C.5.1.21. -/
theorem continuousVectorDifferential_criteria [T2Space E]
    {U : Set (Fin n → 𝕜)} (hU : IsOpen U) (f : (Fin n → 𝕜) → E) :
    (ContinuousVectorDifferential f U ↔ WeakEValuedDifferential f U) ∧
    (EValuedCoordinateDerivatives f U ↔ WeakEValuedDifferential f U) ∧
    (EValuedContinuousGateaux f U ↔ WeakEValuedDifferential f U) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨A, B, hAc, hB, hBA⟩
    refine ⟨A, hAc, fun ℓ x hx => ?_⟩
    have he : (ContinuousLinearMap.proj ℓ).comp ((bidualEvaluations (𝕜 := 𝕜)).comp (B x)) =
        (ℓ.restrictScalars 𝕜).comp (A x) := by
      ext v
      change bidualIdentity (B x v) ℓ = ℓ (A x v)
      rw [hBA x hx v]
      rfl
    rw [← he]
    exact bidualEval_fderiv_iff.mp (hB x hx) ℓ
  · rintro ⟨A, hAc, hD⟩
    obtain ⟨B, hB, _, hBA, _⟩ := continuousDifferential_of_Evalued_weakDifferential hU f A hAc hD
    exact ⟨A, B, hAc, hB, fun x _ v => hBA x v⟩
  · rintro ⟨d, hc, hd⟩
    exact ⟨fun x => coordinateDifferential (fun i => d i x),
      continuousOn_coordinateDifferential d hc,
      fun ℓ _ hx => coordinateDifferential_scalar_hasFDerivAt hU f d hc hd ℓ hx⟩
  · rintro ⟨A, hc, hD⟩
    obtain ⟨B, hB, _, hBA, _⟩ := continuousDifferential_of_Evalued_weakDifferential hU f A hc hD
    refine ⟨fun i x => A x (Pi.single i 1), fun i => ?_, fun i x hx ℓ => ?_⟩
    · exact hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, mem_univ _⟩)
    · have hh := hasDerivAt_of_directional_bidual_limit (bidualEval_directional (hB x hx) (Pi.single i 1)) ℓ
      rw [hBA] at hh
      exact hh
  · rintro ⟨G, hc, hlim⟩
    have hfix (v : Fin n → 𝕜) : ContinuousOn (fun x => G x v) U :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, mem_univ _⟩)
    obtain ⟨A, hA, hD, _, _⟩ := strongDifferential_of_Evalued_Gateaux hU f G hlim hfix
    exact ⟨A, hA, hD⟩
  · rintro ⟨A, hc, hD⟩
    obtain ⟨B, hB, _, hBA, _⟩ := continuousDifferential_of_Evalued_weakDifferential hU f A hc hD
    exact ⟨fun x v => A x v, hc, fun x hx v => hBA x v ▸ bidualEval_directional (hB x hx) v⟩

end StrongCoordinates

end StrongDirectional

end Masullo
