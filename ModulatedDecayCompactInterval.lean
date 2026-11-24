import ModulatedDecayFrechet
import DecayLogistic
import BruhatStageEvaluation

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ)

private def endpointDenominator (a b t : ℝ) : ℝ := Real.exp (a*t) + Real.exp (b*t)

private theorem endpointDenominator_ne (a b t : ℝ) : endpointDenominator a b t ≠ 0 :=
  ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))

private theorem exp_mul_inv_endpointDenominator (a b t : ℝ) :
    Real.exp (a*t) * (endpointDenominator a b t)⁻¹ = decayLogistic (b-a) t := by
  have he : Real.exp ((b-a)*t) = Real.exp (b*t) / Real.exp (a*t) := by
    rw [sub_mul, Real.exp_sub]
  unfold endpointDenominator decayLogistic
  rw [he]
  field_simp

private def divideEndpointWeights (a b : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mulLeft ℂ (fun x => (((endpointDenominator a b (m x).toAdd)⁻¹ : ℝ) : ℂ))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem twist_divideEndpointWeights (a b : ℝ) (f : G → ℂ) :
    modulatedExponentialWeight m a (divideEndpointWeights m a b f) =
      fun x => decayLogistic (b-a) (m x).toAdd • f x := by
  funext x
  rw [modulatedExponentialWeight_apply]
  change Real.exp (a * (m x).toAdd) • ((endpointDenominator a b (m x).toAdd)⁻¹ • f x) = _
  rw [smul_smul,exp_mul_inv_endpointDenominator]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem divideEndpointWeights_comm (a b : ℝ) (f : G → ℂ) :
    divideEndpointWeights m a b f = divideEndpointWeights m b a f := by
  funext x
  change (endpointDenominator a b (m x).toAdd)⁻¹ • f x =
    (endpointDenominator b a (m x).toAdd)⁻¹ • f x
  rw [endpointDenominator, endpointDenominator, add_comm]

set_option maxHeartbeats 2500000 in
private theorem exists_stageEndpointMultiplier (p : WholeBruhatStage G) (c : ℝ) :
    ∃ M : p.val.Space →L[ℂ] p.val.Space,
      ∀ u x, p.val.realize (M u) x = decayLogistic c (m x).toAdd • p.val.realize u x := by
  let l := p.logCoordinate m
  have hl : Continuous l := continuous_toAdd.comp
    (((p.val.1.descendHom m (p.val.1.modulation_eq_one_on_kernel m)).continuous.comp
      p.val.2.equiv.symm.continuous).comp continuous_ofAdd)
  let E := p.val.Space
  let e (x : G) : E →L[ℂ] ℂ :=
    ⟨(LinearMap.proj x).comp p.val.realize,p.val.continuous_realize_eval x⟩
  have h (u : E) : ∃ v : E, ∀ x : G, p.val.realize v x =
      decayLogistic c (m x).toAdd • p.val.realize u x := by
    let v : E := ⟨_,elementarySchwartz_mul_boundedLogMultiplier l hl _ (decayLogistic_smooth c)
      (decayLogistic_iteratedDeriv_bounded c) u⟩
    refine ⟨v,fun x => ?_⟩
    rw [p.realize_eq_coordinates, p.realize_eq_coordinates]
    change decayLogistic c (l (p.coordinates x).toAdd) • u (p.coordinates x).toAdd = _
    rw [p.logCoordinate_coordinates]
  exact bruhatStage_exists_clm_of_evaluation p.val p.val id surjective_id
    (fun x => ((decayLogistic c (m x).toAdd : ℝ) : ℂ) • e x) h

set_option maxHeartbeats 2500000 in
private theorem exists_stageDivideEndpoints (p : WholeBruhatStage G) (a b : ℝ) (hab : a ≤ b) :
    ∃ L : p.val.Space →L[ℂ] WholeBruhatDecayStage m (Icc a b) p,
      ∀ u, (L u).val = divideEndpointWeights m a b (p.val.realize u) := by
  let A : Icc a b := ⟨a,left_mem_Icc.mpr hab⟩
  let B : Icc a b := ⟨b,right_mem_Icc.mpr hab⟩
  obtain ⟨U,hU⟩ := exists_stageEndpointMultiplier m p (b-a)
  obtain ⟨V,hV⟩ := exists_stageEndpointMultiplier m p (a-b)
  let W := (divideEndpointWeights m a b).comp p.val.realize
  have hA (u : p.val.Space) : p.val.realize (U u) = modulatedExponentialWeight m a (W u) := by
    change _ = modulatedExponentialWeight m a (divideEndpointWeights m a b (p.val.realize u))
    rw [twist_divideEndpointWeights]
    exact funext (hU u)
  have hB (u : p.val.Space) : p.val.realize (V u) = modulatedExponentialWeight m b (W u) := by
    change _ = modulatedExponentialWeight m b (divideEndpointWeights m a b (p.val.realize u))
    rw [divideEndpointWeights_comm,twist_divideEndpointWeights]
    exact funext (hV u)
  let L₀ := W.codRestrict (wholeBruhatDecayStageSubmodule m (Icc a b) p) (fun u =>
    (Submodule.mem_iInf _).mpr fun c => by
      have ha : modulatedExponentialWeight m a (W u) ∈ bruhatSchwartzSubmodule :=
        ⟨p.val,U u,hA u⟩
      have hb : modulatedExponentialWeight m b (W u) ∈ bruhatSchwartzSubmodule :=
        ⟨p.val,V u,hB u⟩
      exact wholeBruhatStage_exponential_twist_mem_range m p ⟨U u,hA u⟩
        (modulatedExponentialWeight_mem_between m c.property.1 c.property.2 ha hb))
  let L := WholeBruhatDecayStage.algebraicEquiv.symm.toLinearMap.comp L₀
  have hval (u : p.val.Space) : (L u).val = W u := rfl
  have hContA : Continuous ((WholeBruhatDecayStage.twist p A).comp L) := by
    refine U.continuous.congr fun u => ?_
    change U u = WholeBruhatDecayStage.twist p A (L u)
    apply p.val.1.realizeSchwartz_injective p.val.2
    exact (hA u).trans ((congrArg (modulatedExponentialWeight m a) (hval u)).symm.trans
      (WholeBruhatDecayStage.realize_twist p A (L u)).symm)
  have hContB : Continuous ((WholeBruhatDecayStage.twist p B).comp L) := by
    refine V.continuous.congr fun u => ?_
    change V u = WholeBruhatDecayStage.twist p B (L u)
    apply p.val.1.realizeSchwartz_injective p.val.2
    exact (hB u).trans ((congrArg (modulatedExponentialWeight m b) (hval u)).symm.trans
      (WholeBruhatDecayStage.realize_twist p B (L u)).symm)
  refine ⟨⟨L,(WholeBruhatDecayStage.continuous_iff L).mpr fun c => ?_⟩,hval⟩
  exact WholeBruhatDecayStage.continuous_twist_of_bracket m p L
    (a := A) (c := c) (b := B) c.property.1 c.property.2
    hContA hContB

set_option maxHeartbeats 2600000 in
private theorem exists_divideEndpointsCLM (hm : IsProperMap m) (hms : Surjective m)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m (Icc a b),
      ∀ f, (R f).val = divideEndpointWeights m a b f.val := by
  let E := ModulatedExponentialInductive m (Icc a b)
  let D := divideEndpointWeights m a b
  have hStage (p : BruhatSchwartzStage G) :
      ∃ L : p.Space →L[ℂ] E, ∀ u, (L u).val = D (p.realize u) := by
    obtain ⟨q,hq⟩ := exists_wholeBruhatStage_refinement m hm hms p
    obtain ⟨L,hL⟩ := exists_stageDivideEndpoints m q a b hab
    let j : WholeBruhatDecayStage m (Icc a b) q →L[ℂ] E :=
      ⟨ModulatedExponentialInductive.stageMap q,ModulatedExponentialInductive.stageMap_continuous q⟩
    let T := p.transition q.val hq
    refine ⟨j.comp (L.comp T),fun u => ?_⟩
    change (L (T u)).val = D (p.realize u)
    exact (hL (T u)).trans (congrArg D
      (congrArg (fun f : BruhatSchwartz G => f.val) (p.inclusion_transition q.val hq u)))
  have hmem (f : BruhatSchwartz G) :
      D f.val ∈ modulatedExponentialDecaySubmodule m (Icc a b) := by
    obtain ⟨p,u,hu⟩ := f.property
    obtain ⟨L,hL⟩ := hStage p
    have he : (L u).val = D f.val := (hL u).trans (congrArg D hu)
    exact he ▸ (ModulatedExponentialInductive.algebraicEquiv (L u)).property
  let R₀ := ((divideEndpointWeights m a b).comp bruhatSchwartzSubmodule.subtype).codRestrict
    (modulatedExponentialDecaySubmodule m (Icc a b)) hmem
  let A := ModulatedExponentialInductive.algebraicEquiv (m := m) (I := Icc a b)
  let R := A.symm.toLinearMap.comp R₀
  have hR (f : BruhatSchwartz G) : (R f).val = D f.val := rfl
  refine ⟨⟨R,?_⟩,hR⟩
  apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G => p.inclusion) R).mpr
  intro p
  obtain ⟨L,hL⟩ := hStage p
  refine L.continuous.congr fun u => ?_
  have he : (L u).val = (R (p.inclusion u)).val := (hL u).trans (hR (p.inclusion u)).symm
  exact A.injective (Subtype.ext he)

set_option maxHeartbeats 1800000 in
/-- The sum of the two endpoint twists identifies the decay space of a closed
interval with the full Schwartz–Bruhat space. -/
theorem modulatedDecay_endpointSumEquiv (hm : IsProperMap m) (hms : Surjective m)
    (a b : ℝ) (hab : a ≤ b) :
    let A : Icc a b := ⟨a,left_mem_Icc.mpr hab⟩
    let B : Icc a b := ⟨b,right_mem_Icc.mpr hab⟩
    ∃ e : ModulatedExponentialInductive m (Icc a b) ≃L[ℂ] BruhatSchwartz G,
      e.toContinuousLinearMap = modulatedDecayTwistCLM m _ A + modulatedDecayTwistCLM m _ B := by
  intro A B
  let J := modulatedDecayTwistCLM m (Icc a b) A + modulatedDecayTwistCLM m (Icc a b) B
  obtain ⟨R,hR⟩ := exists_divideEndpointsCLM m hm hms a b hab
  have hj (f : ModulatedExponentialInductive m (Icc a b)) (x : G) :
      (J f).val x = endpointDenominator a b (m x).toAdd • f.val x := by
    change Real.exp (a * (m x).toAdd) • f.val x + Real.exp (b * (m x).toAdd) • f.val x = _
    rw [← add_smul]
    rfl
  have hr (f : BruhatSchwartz G) (x : G) :
      (R f).val x = (endpointDenominator a b (m x).toAdd)⁻¹ • f.val x :=
    congrFun (hR f) x
  have hl : LeftInverse R J := by
    intro f
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext x
    change (R (J f)).val x = f.val x
    rw [hr,hj, inv_smul_smul₀ (endpointDenominator_ne a b _)]
  have hright : RightInverse R J := by
    intro f
    apply Subtype.ext
    funext x
    rw [hj,hr,smul_inv_smul₀ (endpointDenominator_ne a b _)]
  exact ⟨ContinuousLinearEquiv.equivOfInverse J R hl hright,rfl⟩

/-- Theorem D.3.3.7(4). On a closed bounded interval, the projective topology
of all the twists is the inductive-limit topology. -/
theorem modulatedDecay_inductive_eq_projective_Icc (hm : IsProperMap m) (hms : Surjective m)
    (a b : ℝ) (hab : a ≤ b) :
    let T (f : ModulatedExponentialInductive m (Icc a b)) (c : Icc a b) :=
      modulatedDecayTwistCLM m (Icc a b) c f
    (inferInstance : TopologicalSpace (ModulatedExponentialInductive m (Icc a b))) =
      TopologicalSpace.induced T inferInstance := by
  intro T
  let A : Icc a b := ⟨a,left_mem_Icc.mpr hab⟩
  let B : Icc a b := ⟨b,right_mem_Icc.mpr hab⟩
  obtain ⟨e,he⟩ := modulatedDecay_endpointSumEquiv m hm hms a b hab
  let P (f : Icc a b → BruhatSchwartz G) := f A + f B
  have hp : Continuous P := (continuous_apply A).add (continuous_apply B)
  have hT : Continuous T := continuous_pi fun c => (modulatedDecayTwistCLM m (Icc a b) c).continuous
  have hPT : P ∘ T = e := by
    funext f
    exact (congrArg (fun L : ModulatedExponentialInductive m (Icc a b) →L[ℂ] BruhatSchwartz G =>
      L f) he).symm
  have hI : IsInducing (P ∘ T) := hPT ▸ e.toHomeomorph.isInducing
  exact (IsInducing.of_comp hT hp hI).eq_induced

/-- The two topologies agree for every nonempty compact real interval. -/
theorem modulatedDecay_inductive_eq_projective_compact (hm : IsProperMap m) (hms : Surjective m)
    (I : Set ℝ) (hI : IsCompact I) (hn : I.Nonempty) (hconn : OrdConnected I) :
    let T (f : ModulatedExponentialInductive m I) (c : I) := modulatedDecayTwistCLM m I c f
    (inferInstance : TopologicalSpace (ModulatedExponentialInductive m I)) =
      TopologicalSpace.induced T inferInstance := by
  obtain ⟨a,ha⟩ := hI.exists_isLeast hn
  obtain ⟨b,hb⟩ := hI.exists_isGreatest hn
  have hEq : I = Icc a b :=
    Subset.antisymm (fun x hx => ⟨ha.2 hx,hb.2 hx⟩) (hconn.out ha.1 hb.1)
  subst I
  exact modulatedDecay_inductive_eq_projective_Icc m hm hms a b (ha.2 hb.1)


end

end Masullo
