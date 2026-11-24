import ModulatedDecayTranslations
import CompactGroupAveraging
import ElementarySchwartzComplete

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]
  (ω : PontryaginDual m.toMonoidHom.ker)

/-- The scalar formula for the normalized compact-kernel character projection. -/
def modulatedKernelAverage (f : G → ℂ) (x : G) : ℂ :=
  ∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x) ∂ν

variable [hprob : IsProbabilityMeasure ν] in
include hprob in
/-- The probability-Haar formula agrees with the volume-normalized
formula for any chosen kernel Haar measure in (D.2.1.2). -/
theorem modulatedKernelAverage_eq_normalized [SecondCountableTopology G] (hm : IsProperMap m)
    (μ : Measure K) [μ.IsHaarMeasure] (f : G → ℂ) (x : G) :
    modulatedKernelAverage m ν ω f x =
      (μ.real univ)⁻¹ • (∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x) ∂μ) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : SecondCountableTopology K := IsInducing.subtypeVal.secondCountableTopology
  let c := Measure.haarScalarFactor μ ν
  have hc : 0 < (c : ℝ) := by
    exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν
  have hμ : μ = c • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  have hν : ν.real univ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [hμ, measureReal_nnreal_smul_apply, hν, mul_one, integral_smul_nnreal_measure]
  change _ = (c : ℝ)⁻¹ • ((c : ℝ) •
    (∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x) ∂ν))
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rfl

private theorem integrable_modulatedKernelAverage (hm : IsProperMap m) {f : G → ℂ}
    (hf : Continuous f) (x : G) :
    Integrable (fun k : K => (((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x)) ν := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  exact ((continuous_subtype_val.comp ω.continuous.inv).mul
    (hf.comp (continuous_subtype_val.inv.mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private def modulatedKernelAverageLinear (hm : IsProperMap m) : C(G, ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := modulatedKernelAverage m ν ω f
  map_add' f g := by
    funext x
    change (∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * (f (k.val⁻¹ * x) + g (k.val⁻¹ * x)) ∂ν) = _
    simp_rw [mul_add]
    exact integral_add (integrable_modulatedKernelAverage m ν ω hm f.continuous x)
      (integrable_modulatedKernelAverage m ν ω hm g.continuous x)
  map_smul' c f := by
    funext x
    change (∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * (c * f (k.val⁻¹ * x)) ∂ν) =
      c * (∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x) ∂ν)
    simp_rw [mul_left_comm _ c]
    exact integral_const_mul _ _

set_option maxHeartbeats 1800000 in
/-- Averaging compact-kernel translations gives a continuous Schwartz
endomorphism on every whole-group elementary stage. -/
private theorem exists_wholeStage_kernelAverage (hm : IsProperMap m) (p : WholeBruhatStage G) :
    ∃ A : p.val.Space →L[ℂ] p.val.Space, ∀ u,
      p.val.realize (A u) = modulatedKernelAverage m ν ω (p.val.realize u) := by
  let P := p.val
  let lift (g : G) : P.1.upper.val := ⟨g, p.property.symm ▸ Subgroup.mem_top g⟩
  letI : ContinuousSMul ℂ P.Space := (PolynormableSpace.withSeminorms ℂ P.Space).continuousSMul
  let ρ (k : K) : P.Space →L[ℂ] P.Space := (((ω k)⁻¹ : Circle) : ℂ) •
    elementarySchwartz_translate (P.1.stageCoordinates P.2 (lift k.val⁻¹)).toAdd
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : T2Space P.Space := elementarySchwartz_t2
  letI : CompleteSpace P.Space := completeSpace_elementarySchwartz
  letI : LocallyConvexSpace ℝ P.Space := (PolynormableSpace.withSeminorms ℂ P.Space).toLocallyConvexSpace
  have hg : Continuous (fun k : K => (P.1.stageCoordinates P.2 (lift k.val⁻¹)).toAdd) :=
    continuous_toAdd.comp ((P.1.stageCoordinates P.2).continuous.comp
      (continuous_subtype_val.inv.subtype_mk _))
  have ht : Continuous (fun z : K × P.Space =>
      elementarySchwartz_translate (P.1.stageCoordinates P.2 (lift z.1.val⁻¹)).toAdd z.2) :=
    (@continuous_elementarySchwartz_translate P.2.realDim P.2.torusDim P.2.latticeRank
      P.2.finiteFactor P.2.finiteGroup P.2.finiteTopology P.2.finiteDiscrete (Finite.of_fintype _)).comp
      ((hg.comp continuous_fst).prodMk continuous_snd)
  have hρ : Continuous (fun z : K × P.Space => ρ z.1 z.2) :=
    ((continuous_subtype_val.comp ω.continuous.inv).comp continuous_fst).smul ht
  obtain ⟨A, hA⟩ := compactPettis_clm_exists ν ρ hρ
  refine ⟨A, fun u => funext fun x => ?_⟩
  let ev : P.Space →L[ℂ] ℂ :=
    ⟨(LinearMap.proj x).comp P.realize, P.continuous_realize_eval x⟩
  have he := (hA u ev).2
  change P.realize (A u) x = ∫ k : K, P.realize (ρ k u) x ∂ν at he
  rw [he]
  apply integral_congr_ae
  refine .of_forall fun k => ?_
  change P.realize ((((ω k)⁻¹ : Circle) : ℂ) •
    elementarySchwartz_translate (P.1.stageCoordinates P.2 (lift k.val⁻¹)).toAdd u) x =
    (((ω k)⁻¹ : Circle) : ℂ) * P.realize u (k.val⁻¹ * x)
  rw [map_smul, P.realize_translate]
  change _ * P.realize u (x * k.val⁻¹) = _
  rw [mul_comm x]

private theorem modulatedKernelAverage_weight (a : ℝ) (f : G → ℂ) :
    modulatedExponentialWeight m a (modulatedKernelAverage m ν ω f) =
      modulatedKernelAverage m ν ω (modulatedExponentialWeight m a f) := by
  funext x
  rw [modulatedExponentialWeight_apply, modulatedKernelAverage, modulatedKernelAverage, ← integral_smul]
  apply integral_congr_ae
  refine .of_forall fun k => ?_
  change Real.exp (a * (m x).toAdd) • ((((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x)) =
    (((ω k)⁻¹ : Circle) : ℂ) * modulatedExponentialWeight m a f (k.val⁻¹ * x)
  rw [modulatedExponentialWeight_apply, map_mul, map_inv, show m k.val = 1 from k.property,
    inv_one, one_mul, mul_smul_comm]

set_option maxHeartbeats 1800000 in
/-- The normalized compact-kernel character projection on the Schwartz–Bruhat space. -/
def bruhatSchwartz_kernelAverage (hm : IsProperMap m) (hms : Surjective m) :
    BruhatSchwartz G →L[ℂ] BruhatSchwartz G := by
  let E : BruhatSchwartz G →ₗ[ℂ] C(G, ℂ) :=
    { toFun := fun f => ⟨f.val, bruhatSchwartz_continuous f⟩
      map_add' := fun _ _ => DFunLike.ext _ _ fun _ => rfl
      map_smul' := fun _ _ => DFunLike.ext _ _ fun _ => rfl }
  let A := (modulatedKernelAverageLinear m ν ω hm).comp E
  have hmem (f : BruhatSchwartz G) : A f ∈ bruhatSchwartzSubmodule (G := G) := by
    obtain ⟨p, u, hu⟩ := f.property
    obtain ⟨q, hpq⟩ := exists_wholeBruhatStage_refinement m hm hms p
    obtain ⟨L, hL⟩ := exists_wholeStage_kernelAverage m ν ω hm q
    let v := p.transition q.val hpq u
    have hv : q.val.realize v = f.val := (congrArg Subtype.val (p.inclusion_transition q.val hpq u)).trans hu
    exact ⟨q.val, L v, (hL v).trans (congrArg (modulatedKernelAverage m ν ω) hv)⟩
  let A₀ := A.codRestrict _ hmem
  refine ⟨A₀, (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G => p.inclusion) A₀).mpr ?_⟩
  intro p
  obtain ⟨q, hpq⟩ := exists_wholeBruhatStage_refinement m hm hms p
  obtain ⟨L, hL⟩ := exists_wholeStage_kernelAverage m ν ω hm q
  let T := p.transition q.val hpq
  have he : (A₀.comp p.inclusion : p.Space → BruhatSchwartz G) = q.val.inclusionCLM ∘ L ∘ T := by
    funext u
    apply Subtype.ext
    have hv := congrArg Subtype.val (p.inclusion_transition q.val hpq u)
    exact ((hL (T u)).trans (congrArg (modulatedKernelAverage m ν ω) hv)).symm
  rw [he]
  exact q.val.inclusionCLM.continuous.comp (L.continuous.comp T.continuous)

theorem bruhatSchwartz_kernelAverage_apply (hm : IsProperMap m) (hms : Surjective m)
    (f : BruhatSchwartz G) :
    (bruhatSchwartz_kernelAverage m ν ω hm hms f).val = modulatedKernelAverage m ν ω f.val := rfl

variable (I : Set ℝ)

private theorem inductiveDecay_continuous_value (hI : I.Nonempty) (f : ModulatedExponentialInductive m I) :
    Continuous f.val := by
  obtain ⟨a, ha⟩ := hI
  let u := modulatedExponentialDecay_twist m I ⟨a, ha⟩ (ModulatedExponentialInductive.algebraicEquiv f)
  have hu : Continuous (fun g => Real.exp (-a * (m g).toAdd) • u.val g) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_toAdd.comp m.continuous))).smul
      (bruhatSchwartz_continuous u)
  apply hu.congr
  intro g
  change Real.exp (-a * (m g).toAdd) • (Real.exp (a * (m g).toAdd) • f.val g) = f.val g
  rw [smul_smul, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_smul]

set_option maxHeartbeats 2200000 in
/-- The compact-kernel average preserves modulated decay and is continuous
for the inductive topology. -/
def modulatedDecay_kernelAverage (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    ModulatedExponentialInductive m I →L[ℂ] ModulatedExponentialInductive m I := by
  let E : ModulatedExponentialInductive m I →ₗ[ℂ] C(G, ℂ) :=
    { toFun := fun f => ⟨f.val, inductiveDecay_continuous_value m I hI f⟩
      map_add' := fun _ _ => DFunLike.ext _ _ fun _ => rfl
      map_smul' := fun _ _ => DFunLike.ext _ _ fun _ => rfl }
  let A := (modulatedKernelAverageLinear m ν ω hm).comp E
  have hmem (f : ModulatedExponentialInductive m I) : A f ∈ modulatedExponentialDecaySubmodule m I := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    let u := modulatedExponentialDecay_twist m I a (ModulatedExponentialInductive.algebraicEquiv f)
    change modulatedExponentialWeight m a (modulatedKernelAverage m ν ω f.val) ∈ bruhatSchwartzSubmodule
    rw [modulatedKernelAverage_weight]
    exact (bruhatSchwartz_kernelAverage m ν ω hm hms u).property
  let A₀ := ModulatedExponentialInductive.algebraicEquiv.symm.toLinearMap.comp (A.codRestrict _ hmem)
  refine ⟨A₀, (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G => ModulatedExponentialInductive.stageMap (m := m) (I := I) p)
    A₀).mpr fun p => ?_⟩
  obtain ⟨L, hL⟩ := exists_wholeStage_kernelAverage m ν ω hm p
  have hT (a : I) (u : WholeBruhatDecayStage m I p) :
      p.val.realize (L (WholeBruhatDecayStage.twist p a u)) =
        modulatedExponentialWeight m a (modulatedKernelAverage m ν ω u.val) := by
    rw [hL, WholeBruhatDecayStage.realize_twist, modulatedKernelAverage_weight]
  let U (u : WholeBruhatDecayStage m I p) : WholeBruhatDecayStage m I p :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨modulatedKernelAverage m ν ω u.val,
      (Submodule.mem_iInf _).mpr fun a => ⟨L (WholeBruhatDecayStage.twist p a u), hT a u⟩⟩
  have hU : Continuous U := by
    apply (WholeBruhatDecayStage.continuous_iff U).mpr
    intro a
    have he : WholeBruhatDecayStage.twist p a ∘ U = L ∘ WholeBruhatDecayStage.twist p a := by
      funext u
      apply p.val.1.realizeSchwartz_injective p.val.2
      exact (WholeBruhatDecayStage.realize_twist p a (U u)).trans (hT a u).symm
    rw [he]
    exact L.continuous.comp ((WholeBruhatDecayStage.continuous_iff (id : WholeBruhatDecayStage m I p → _)).mp
      continuous_id a)
  have he : (A₀.comp (ModulatedExponentialInductive.stageMap p) :
      WholeBruhatDecayStage m I p → ModulatedExponentialInductive m I) =
      ModulatedExponentialInductive.stageMap p ∘ U := by
    funext u
    exact ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext rfl)
  rw [he]
  exact (ModulatedExponentialInductive.stageMap_continuous p).comp hU

theorem modulatedDecay_kernelAverage_apply (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (f : ModulatedExponentialInductive m I) :
    (modulatedDecay_kernelAverage m ν ω I hm hms hI f).val = modulatedKernelAverage m ν ω f.val := rfl

theorem modulatedKernelAverage_eigen (f : G → ℂ) (k : K) (x : G) :
    modulatedKernelAverage m ν ω f (k.val⁻¹ * x) = (ω k : ℂ) * modulatedKernelAverage m ν ω f x := by
  let F₀ (s : K) := (((ω s)⁻¹ : Circle) : ℂ) * f (s.val⁻¹ * x)
  have h := integral_mul_left_eq_self (μ := ν) F₀ k
  change (∫ s : K, (((ω s)⁻¹ : Circle) : ℂ) * f (s.val⁻¹ * (k.val⁻¹ * x)) ∂ν) =
    (ω k : ℂ) * ∫ s : K, F₀ s ∂ν
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun s => ?_
  change (((ω s)⁻¹ : Circle) : ℂ) * f (s.val⁻¹ * (k.val⁻¹ * x)) =
    (ω k : ℂ) * ((((ω (k * s))⁻¹ : Circle) : ℂ) * f ((↑(k * s) : G)⁻¹ * x))
  have he : (ω k : ℂ) * (((ω (k * s))⁻¹ : Circle) : ℂ) = (((ω s)⁻¹ : Circle) : ℂ) := by
    rw [← Circle.coe_mul, map_mul]
    congr 1
    calc
      _ = (ω s)⁻¹ * (ω k * (ω k)⁻¹) := by rw [mul_inv_rev]; ac_rfl
      _ = _ := by simp
  have harg : (↑(k * s) : G)⁻¹ * x = s.val⁻¹ * (k.val⁻¹ * x) := by
    change (k.val * s.val)⁻¹ * x = _
    rw [mul_inv_rev, mul_assoc]
  calc
    _ = ((ω k : ℂ) * (((ω (k * s))⁻¹ : Circle) : ℂ)) * f ((↑(k * s) : G)⁻¹ * x) :=
      (congrArg₂ (· * ·) he (congrArg f harg)).symm
    _ = _ := mul_assoc _ _ _

variable [hprob : IsProbabilityMeasure ν] in
include hprob in
private theorem modulatedKernelAverage_fixes {f : G → ℂ}
    (hf : ∀ (k : K) (x : G), f (k.val⁻¹ * x) = (ω k : ℂ) * f x) :
    modulatedKernelAverage m ν ω f = f := by
  funext x
  unfold modulatedKernelAverage
  calc
    _ = ∫ _ : K, f x ∂ν := by
      apply integral_congr_ae
      refine .of_forall fun k => ?_
      change (((ω k)⁻¹ : Circle) : ℂ) * f (k.val⁻¹ * x) = f x
      rw [hf, ← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
    _ = ν.real univ • f x := integral_const _
    _ = _ := by rw [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- The compact-kernel character isotype, with its topology induced from
the exponential decay space. -/
def modulatedDecayIsotype : Submodule ℂ (ModulatedExponentialInductive m I) where
  carrier := {f | ∀ (k : K) (x : G), f.val (k.val⁻¹ * x) = (ω k : ℂ) * f.val x}
  zero_mem' := by intro k x; change (0 : ℂ) = (ω k : ℂ) * 0; rw [mul_zero]
  add_mem' {f g} hf hg k x := by
    change f.val (k.val⁻¹ * x) + g.val (k.val⁻¹ * x) =
      (ω k : ℂ) * (f.val x + g.val x)
    rw [hf k x, hg k x, mul_add]
  smul_mem' c f hf k x := by
    change c * f.val (k.val⁻¹ * x) = (ω k : ℂ) * (c * f.val x)
    rw [hf k x, mul_left_comm]

set_option maxHeartbeats 1300000 in
/-- Twisting into the full Schwartz–Bruhat space is continuous from the
inductive decay space at every abscissa. -/
def modulatedDecayTwistCLM (a : I) : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz G := by
  let L := (modulatedExponentialDecay_twist m I a).comp ModulatedExponentialInductive.algebraicEquiv.toLinearMap
  refine ⟨L, (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G => ModulatedExponentialInductive.stageMap (m := m) (I := I) p)
    L).mpr fun p => ?_⟩
  have he : (L.comp (ModulatedExponentialInductive.stageMap p) : WholeBruhatDecayStage m I p → BruhatSchwartz G) =
      p.val.inclusionCLM ∘ WholeBruhatDecayStage.twist p a := by
    funext u
    exact Subtype.ext (WholeBruhatDecayStage.realize_twist p a u).symm
  rw [he]
  exact p.val.inclusionCLM.continuous.comp
    ((WholeBruhatDecayStage.continuous_iff (id : WholeBruhatDecayStage m I p → _)).mp continuous_id a)

set_option maxHeartbeats 2200000 in
variable [hprob : IsProbabilityMeasure ν] in
include hprob in
/-- The projection onto the compact character isotype commutes with all
abscissa twists. It is the unique linear map doing so and is open onto
the isotype. -/
theorem modulatedDecay_existsUnique_isotypeProjection
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    ∃! P : ModulatedExponentialInductive m I →ₗ[ℂ] modulatedDecayIsotype m ω I,
      (∀ a f, modulatedDecayTwistCLM m I a (P f).val =
        bruhatSchwartz_kernelAverage m ν ω hm hms (modulatedDecayTwistCLM m I a f)) ∧
      Continuous P ∧ IsOpenMap P ∧ Surjective P ∧ ∀ f : modulatedDecayIsotype m ω I, P f.val = f := by
  let A := modulatedDecay_kernelAverage m ν ω I hm hms hI
  let U := modulatedDecayIsotype m ω I
  let P : ModulatedExponentialInductive m I →L[ℂ] U :=
    A.codRestrict U (fun f k x => modulatedKernelAverage_eigen m ν ω f.val k x)
  have hP (f : U) : P f.val = f := by
    apply Subtype.ext
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    exact Subtype.ext (modulatedKernelAverage_fixes m ν ω f.property)
  have hcomm (a : I) (f : ModulatedExponentialInductive m I) :
      modulatedDecayTwistCLM m I a (P f).val =
        bruhatSchwartz_kernelAverage m ν ω hm hms (modulatedDecayTwistCLM m I a f) := by
    apply Subtype.ext
    exact modulatedKernelAverage_weight m ν ω a f.val
  letI : IsTopologicalAddGroup (ModulatedExponentialInductive m I) :=
    (PolynormableSpace.withSeminorms ℂ (ModulatedExponentialInductive m I)).topologicalAddGroup
  have hopen : IsOpenMap P := by
    apply IsOpenMap.of_sections
    intro y
    let s (u : U) := y + (u - P y).val
    refine ⟨s, (continuous_const.add (continuous_subtype_val.comp
      (continuous_id.sub continuous_const))).continuousAt, ?_, fun z => ?_⟩
    · change y + (P y - P y).val = y
      rw [sub_self]
      exact add_zero y
    · change P (y + (z - P y).val) = z
      rw [map_add, hP]
      abel
  refine ⟨P.toLinearMap, ⟨hcomm, P.continuous, hopen, fun f => ⟨f.val, hP f⟩, hP⟩, fun R hR => ?_⟩
  ext f : 1
  apply Subtype.ext
  apply ModulatedExponentialInductive.algebraicEquiv.injective
  apply Subtype.ext
  funext x
  obtain ⟨a, ha⟩ := hI
  let a₀ : I := ⟨a, ha⟩
  have he := congrArg (fun u : BruhatSchwartz G => u.val x) ((hR.1 a₀ f).trans (hcomm a₀ f).symm)
  change Real.exp (a * (m x).toAdd) • (R f).val.val x =
    Real.exp (a * (m x).toAdd) • (P f).val.val x at he
  exact (smul_right_injective ℂ (Real.exp_ne_zero _)) he

end

end Masullo
