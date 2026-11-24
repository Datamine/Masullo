import ModulatedDecayTopology
import StrictLimitCompleteness

open Bornology Function Set Topology
open scoped Uniformity

namespace Masullo

open LinearInductivePresentation

noncomputable section

universe u

set_option maxHeartbeats 2100000

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

private theorem transition_realize (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1)
    (a : I) (f : WholeBruhatDecayStage m I p) :
    q.val.realize (p.val.transition q.val hpq (WholeBruhatDecayStage.twist p a f)) =
      modulatedExponentialWeight m a f.val := by
  have h := p.val.inclusion_transition q.val hpq (WholeBruhatDecayStage.twist p a f)
  have hv := congrArg (fun g : BruhatSchwartz G => g.val) h
  exact hv.trans (WholeBruhatDecayStage.realize_twist p a f)

private def stageTransitionSubmodule (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1) :
    WholeBruhatDecayStage m I p →ₗ[ℂ] wholeBruhatDecayStageSubmodule m I q := by
  let A := WholeBruhatDecayStage.algebraicEquiv (m := m) (I := I) (p := p)
  let L := (wholeBruhatDecayStageSubmodule m I p).subtype.comp A.toLinearMap
  exact L.codRestrict (wholeBruhatDecayStageSubmodule m I q)
    (fun f => (Submodule.mem_iInf _).mpr fun a =>
      ⟨p.val.transition q.val hpq (WholeBruhatDecayStage.twist p a f),
        transition_realize m I p q hpq a f⟩)

private def stageTransitionLinear (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1) :
    WholeBruhatDecayStage m I p →ₗ[ℂ] WholeBruhatDecayStage m I q :=
  WholeBruhatDecayStage.algebraicEquiv.symm.toLinearMap.comp (stageTransitionSubmodule m I p q hpq)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem stageVal_algebraicEquiv_symm (q : WholeBruhatStage G)
    (z : wholeBruhatDecayStageSubmodule m I q) :
    (WholeBruhatDecayStage.algebraicEquiv.symm z).val = z.val := by
  simp only [WholeBruhatDecayStage.val, LinearEquiv.apply_symm_apply]

private theorem stageTransitionLinear_val (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1)
    (f : WholeBruhatDecayStage m I p) : (stageTransitionLinear m I p q hpq f).val = f.val := by
  let z := stageTransitionSubmodule m I p q hpq f
  have hz : z.val = f.val := rfl
  change (WholeBruhatDecayStage.algebraicEquiv.symm z).val = f.val
  exact (stageVal_algebraicEquiv_symm m I q z).trans hz

/-- Refinement preserves the underlying function and transports every twist. -/
def wholeBruhatDecayStageTransition (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1) :
    WholeBruhatDecayStage m I p →L[ℂ] WholeBruhatDecayStage m I q := by
  let L := stageTransitionLinear m I p q hpq
  let T := p.val.transition q.val hpq
  refine ⟨L,(WholeBruhatDecayStage.continuous_iff L).mpr fun a => ?_⟩
  have hTw : Continuous (WholeBruhatDecayStage.twist p a : WholeBruhatDecayStage m I p → p.val.Space) :=
    (WholeBruhatDecayStage.continuous_iff (id : WholeBruhatDecayStage m I p → _)).mp continuous_id a
  refine (T.continuous.comp hTw).congr fun f => ?_
  apply q.val.1.realizeSchwartz_injective q.val.2
  have hv : modulatedExponentialWeight m a (L f).val = modulatedExponentialWeight m a f.val :=
    congrArg (modulatedExponentialWeight m a) (stageTransitionLinear_val m I p q hpq f)
  exact (transition_realize m I p q hpq a f).trans
    (hv.symm.trans (WholeBruhatDecayStage.realize_twist q a (L f)).symm)

private abbrev inclusion (p : WholeBruhatStage G) :
    WholeBruhatDecayStage m I p →L[ℂ] ModulatedExponentialInductive m I :=
  ⟨ModulatedExponentialInductive.stageMap p,ModulatedExponentialInductive.stageMap_continuous p⟩

private theorem transition_val (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1)
    (f : WholeBruhatDecayStage m I p) : (wholeBruhatDecayStageTransition m I p q hpq f).val = f.val :=
  stageTransitionLinear_val m I p q hpq f

/-- Refinement preserves the underlying function. -/
theorem wholeBruhatDecayStageTransition_val (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1)
    (f : WholeBruhatDecayStage m I p) : (wholeBruhatDecayStageTransition m I p q hpq f).val = f.val :=
  transition_val m I p q hpq f

private theorem inclusion_val (p : WholeBruhatStage G) (f : WholeBruhatDecayStage m I p) :
    (inclusion m I p f).val = f.val :=
  rfl

private theorem inclusion_transition (p q : WholeBruhatStage G) (hpq : p.val.1 ≤ q.val.1)
    (f : WholeBruhatDecayStage m I p) :
    inclusion m I q (wholeBruhatDecayStageTransition m I p q hpq f) = inclusion m I p f := by
  let A := ModulatedExponentialInductive.algebraicEquiv (m := m) (I := I)
  let T := wholeBruhatDecayStageTransition m I p q hpq
  have h : (inclusion m I q (T f)).val = (inclusion m I p f).val :=
    (inclusion_val m I q (T f)).trans ((transition_val m I p q hpq f).trans (inclusion_val m I p f).symm)
  have he : A (inclusion m I q (T f)) = A (inclusion m I p f) := Subtype.ext h
  exact A.injective he

private theorem stageSeminorm_continuous_of_cofinal (p : ℕ → WholeBruhatStage G)
    (hCov : ∀ q : WholeBruhatStage G, ∃ n, q.val.1 ≤ (p n).val.1)
    (s : Seminorm ℂ (ModulatedExponentialInductive m I))
    (hs : ∀ n, Continuous (s.comp (inclusion m I (p n)).toLinearMap)) : Continuous s := by
  apply locallyConvexFinal_seminorm_continuous
    (fun q : WholeBruhatStage G => ModulatedExponentialInductive.stageMap (m := m) (I := I) q)
  intro q
  obtain ⟨n,hn⟩ := hCov q
  exact ((hs n).comp (wholeBruhatDecayStageTransition m I q (p n) hn).continuous).congr
    (fun f => congrArg s (inclusion_transition m I q (p n) hn f))

private def decayPresentation [SecondCountableTopology G] (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (p : ℕ → WholeBruhatStage G) (hp : Monotone (fun n => (p n).val.1))
    (hCov : ∀ q : WholeBruhatStage G, ∃ n, q.val.1 ≤ (p n).val.1) :
    LinearInductivePresentation (ModulatedExponentialInductive m I)
      (fun n => WholeBruhatDecayStage m I (p n)) where
  incl n := inclusion m I (p n)
  transition {k n} h := wholeBruhatDecayStageTransition m I (p k) (p n) (hp h)
  injective_incl n := (wholeBruhatDecayStage_isEmbedding m I hI (p n)).injective
  incl_transition {k n} h f := inclusion_transition m I (p k) (p n) (hp h) f
  exhaust f := by
    obtain ⟨q,hq⟩ := exists_wholeBruhatStage_decay m I hm hms hI
      (ModulatedExponentialInductive.algebraicEquiv f)
    let z : wholeBruhatDecayStageSubmodule m I q := ⟨f.val,(Submodule.mem_iInf _).mpr hq⟩
    let g : WholeBruhatDecayStage m I q := WholeBruhatDecayStage.algebraicEquiv.symm z
    let A := ModulatedExponentialInductive.algebraicEquiv (m := m) (I := I)
    have hv : (inclusion m I q g).val = f.val :=
      (inclusion_val m I q g).trans (stageVal_algebraicEquiv_symm m I q z)
    have he : A (inclusion m I q g) = A f := Subtype.ext hv
    obtain ⟨n,hn⟩ := hCov q
    exact ⟨n,wholeBruhatDecayStageTransition m I q (p n) hn g,
      (inclusion_transition m I q (p n) hn g).trans (A.injective he)⟩
  continuous_limit L := by
    refine ⟨fun h n => h.comp (inclusion m I (p n)).continuous,fun h => ?_⟩
    apply (locallyConvexFinal_continuous_iff
      (fun q : WholeBruhatStage G => ModulatedExponentialInductive.stageMap (m := m) (I := I) q) L).mpr
    intro q
    obtain ⟨n,hn⟩ := hCov q
    exact ((h n).comp (wholeBruhatDecayStageTransition m I q (p n) hn).continuous).congr
      (fun f => congrArg L (inclusion_transition m I q (p n) hn f))

/-- A continuous linear map on the full decay space is determined on any
increasing cofinal sequence of decay stages. -/
theorem continuousLinearMap_ext_on_cofinal_decayStages [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (p : ℕ → WholeBruhatStage G) (hp : Monotone (fun n => (p n).val.1))
    (hCov : ∀ q : WholeBruhatStage G, ∃ n, q.val.1 ≤ (p n).val.1)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    {F F' : ModulatedExponentialInductive m I →L[ℂ] Y}
    (h : ∀ n x, F (ModulatedExponentialInductive.stageMap (p n) x) =
      F' (ModulatedExponentialInductive.stageMap (p n) x)) : F = F' := by
  let D := decayPresentation m I hm hms hI p hp hCov
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨n, y, rfl⟩ := D.exhaust x
  exact h n y

/-- Compatible continuous maps on cofinal decay stages glue continuously
for the full inductive decay topology. -/
theorem exists_continuousLinearMap_of_cofinal_decayStages [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (p : ℕ → WholeBruhatStage G) (hp : Monotone (fun n => (p n).val.1))
    (hCov : ∀ q : WholeBruhatStage G, ∃ n, q.val.1 ≤ (p n).val.1)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (B : ∀ n, WholeBruhatDecayStage m I (p n) →L[ℂ] Y)
    (hB : ∀ k n (h : k ≤ n) (x : WholeBruhatDecayStage m I (p k)),
      B n (wholeBruhatDecayStageTransition m I (p k) (p n) (hp h) x) = B k x) :
    ∃ L : ModulatedExponentialInductive m I →L[ℂ] Y,
      ∀ n x, L (ModulatedExponentialInductive.stageMap (p n) x) = B n x := by
  let E := ModulatedExponentialInductive m I
  let D := decayPresentation m I hm hms hI p hp hCov
  let L := D.linearMapOfCompatible (fun n => (B n).toLinearMap) hB
  have hL (n : ℕ) (x : WholeBruhatDecayStage m I (p n)) : L (D.incl n x) = B n x :=
    D.linearMapOfCompatible_incl (fun n => (B n).toLinearMap) hB n x
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  have hc : Continuous L := by
    apply ((PolynormableSpace.withSeminorms ℂ Y).continuous_iff_continuous_comp L).mpr
    intro q
    apply stageSeminorm_continuous_of_cofinal m I p hCov
    intro n
    have he : (q.val.comp L).comp (inclusion m I (p n)).toLinearMap = q.val.comp (B n).toLinearMap :=
      Seminorm.ext fun x => congrArg q.val (hL n x)
    rw [he]
    exact q.property.comp (B n).continuous
  exact ⟨⟨L,hc⟩, hL⟩

/-- The additive uniformity of the full inductive decay topology. -/
abbrev modulatedDecayUniformSpace : UniformSpace (ModulatedExponentialInductive m I) :=
  letI : IsTopologicalAddGroup (ModulatedExponentialInductive m I) :=
    (PolynormableSpace.withSeminorms ℂ (ModulatedExponentialInductive m I)).topologicalAddGroup
  IsTopologicalAddGroup.rightUniformSpace _

/-- Theorem D.3.3.7(2). The actual decay space is a countable strict limit,
and is complete, nuclear and Montel. -/
theorem modulatedDecay_complete_nuclear_montel [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    @CompleteSpace (ModulatedExponentialInductive m I) (modulatedDecayUniformSpace m I) ∧
      NuclearLocallyConvex.{u,u} (ModulatedExponentialInductive m I) ∧
      MontelSpace ℂ (ModulatedExponentialInductive m I) := by
  obtain ⟨p,hp,hCov⟩ := exists_wholeBruhatStage_cofinal m hm hms
  let D := decayPresentation m I hm hms hI p hp hCov
  let E := ModulatedExponentialInductive m I
  letI : T2Space E := ModulatedExponentialInductive.t2 m I hI
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : UniformSpace E := modulatedDecayUniformSpace m I
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace E := D.complete_of_strict
    (fun n => WholeBruhatDecayStage.complete m I hI (p n))
    (fun n => wholeBruhatDecayStage_isEmbedding m I hI (p n))
    (stageSeminorm_continuous_of_cofinal m I p hCov)
  have hN : NuclearLocallyConvex.{u,u} E := D.nuclear_of_stages
    (fun n => (wholeBruhatDecayStage_separableNuclearFrechet m hI (p n)).2.1)
    (stageSeminorm_continuous_of_cofinal m I p hCov)
  exact ⟨inferInstance,hN,⟨fun _ hs hb => (nuclearLocallyConvex_totallyBounded hN hb).isCompact_of_isClosed hs⟩⟩

/-- The cofinal Fréchet stages embed with closed image in the inductive limit. -/
theorem modulatedDecay_strictPresentation [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    ∃ (p : ℕ → WholeBruhatStage G) (D : LinearInductivePresentation
      (ModulatedExponentialInductive m I) (fun n => WholeBruhatDecayStage m I (p n))),
      (∀ n, IsFrechetTVS (WholeBruhatDecayStage m I (p n))) ∧
      ∀ n, IsClosedEmbedding (D.incl n) := by
  obtain ⟨p,hp,hCov⟩ := exists_wholeBruhatStage_cofinal m hm hms
  refine ⟨p,decayPresentation m I hm hms hI p hp hCov,fun n =>
    (wholeBruhatDecayStage_separableNuclearFrechet m hI (p n)).2.2,fun n => ?_⟩
  let E := ModulatedExponentialInductive m I
  let X := WholeBruhatDecayStage m I (p n)
  let j : X →L[ℂ] E := inclusion m I (p n)
  letI : T2Space E := ModulatedExponentialInductive.t2 m I hI
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : UniformSpace E := modulatedDecayUniformSpace m I
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := WholeBruhatDecayStage.complete m I hI (p n)
  have h := wholeBruhatDecayStage_isEmbedding m I hI (p n)
  exact ⟨h, (AddMonoidHom.isUniformInducing_of_isInducing
    (f := j.toLinearMap.toAddMonoidHom) h.isInducing).isComplete_range.isClosed⟩

/-- A bounded set is covered by the image of a bounded family in a single
cofinal stage. This gives the topology of the compatible dual. -/
private theorem decayPresentation_bounded_cover [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (p : ℕ → WholeBruhatStage G) (hp : Monotone (fun n => (p n).val.1))
    (hCov : ∀ q : WholeBruhatStage G, ∃ n, q.val.1 ≤ (p n).val.1) :
    ∀ B : Set (ModulatedExponentialInductive m I), IsVonNBounded ℂ B →
      ∃ n C, IsVonNBounded ℂ C ∧ B ⊆ (decayPresentation m I hm hms hI p hp hCov).incl n '' C := by
  intro B hB
  obtain ⟨q,C,hC,hBC⟩ := modulatedDecay_bounded_lift_of_twists m I hm hms hI B
    (fun a => hB.image (modulatedDecayTwistCLM m I a))
  obtain ⟨n,hn⟩ := hCov q
  let T := wholeBruhatDecayStageTransition m I q (p n) hn
  refine ⟨n,T '' C,hC.image T,?_⟩
  rw [← hBC]
  rintro _ ⟨f,hf,rfl⟩
  exact ⟨T f,mem_image_of_mem T hf,inclusion_transition m I q (p n) hn f⟩

/-- Theorem D.3.3.7(3). The strong decay dual is complete, nuclear, and Montel. -/
theorem modulatedDecay_strongDual_complete_nuclear_montel [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    CompleteSpace (StrongDual ℂ (ModulatedExponentialInductive m I)) ∧
      NuclearLocallyConvex.{u,u} (StrongDual ℂ (ModulatedExponentialInductive m I)) ∧
      MontelSpace ℂ (StrongDual ℂ (ModulatedExponentialInductive m I)) := by
  obtain ⟨p,hp,hCov⟩ := exists_wholeBruhatStage_cofinal m hm hms
  let D := decayPresentation m I hm hms hI p hp hCov
  let Y := StrongDual ℂ (ModulatedExponentialInductive m I)
  let X (n : ℕ) := WholeBruhatDecayStage m I (p n)
  let e := D.strongDualRestriction (decayPresentation_bounded_cover m I hm hms hI p hp hCov)
  have hStage (n : ℕ) := wholeBruhatDecayStage_separableNuclearFrechet m hI (p n)
  letI (n : ℕ) : ContinuousSMul ℂ (X n) := (PolynormableSpace.withSeminorms ℂ (X n)).continuousSMul
  letI (n : ℕ) : TopologicalSpace.MetrizableSpace (X n) :=
    (wholeBruhatDecayStage_metrizable_secondCountable m hI (p n)).1
  letI (n : ℕ) : CompleteSpace (StrongDual ℂ (X n)) := inferInstance
  have hclosed : IsClosed (D.CompatibleDual : Set (∀ n, StrongDual ℂ (X n))) := by
    have heq : (D.CompatibleDual : Set (∀ n, StrongDual ℂ (X n))) =
        ⋂ k : ℕ, ⋂ n : ℕ, ⋂ h : k ≤ n, ⋂ x : X k,
          {g : ∀ n, StrongDual ℂ (X n) | g n (D.transition h x) = g k x} := by
      ext g
      simp only [mem_iInter, mem_ofPred_eq]
      rfl
    rw [heq]
    exact isClosed_iInter fun k => isClosed_iInter fun n => isClosed_iInter fun h =>
      isClosed_iInter fun x => isClosed_eq
        ((continuous_eval_const (D.transition h x)).comp (continuous_apply n))
        ((continuous_eval_const x).comp (continuous_apply k))
  let L : Y →+ (∀ n, StrongDual ℂ (X n)) :=
    (D.CompatibleDual.subtype.comp e.toLinearEquiv.toLinearMap).toAddMonoidHom
  have hu : IsUniformInducing L := AddMonoidHom.isUniformInducing_of_isInducing
    (IsInducing.subtypeVal.comp e.toHomeomorph.isInducing)
  have hRange : range L = (D.CompatibleDual : Set (∀ n, StrongDual ℂ (X n))) := by
    ext g
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).property
    · intro hg
      obtain ⟨x,hx⟩ := e.surjective ⟨g,hg⟩
      exact ⟨x,congrArg Subtype.val hx⟩
  letI : CompleteSpace Y := hu.completeSpace (hRange.symm ▸ hclosed.isComplete)
  have hN : NuclearLocallyConvex.{u,u} Y := nuclearLocallyConvex_of_equiv e.symm
    (nuclearLocallyConvex_submodule (nuclearLocallyConvex_pi (fun n =>
      strongDual_nuclear_of_nuclear_frechet (hStage n).2.2 (hStage n).2.1)) D.CompatibleDual)
  exact ⟨inferInstance,hN,⟨fun _ hs hb => (nuclearLocallyConvex_totallyBounded hN hb).isCompact_of_isClosed hs⟩⟩



end

end Masullo
