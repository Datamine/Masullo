import ElementaryRadialSchwartz
import MellinBergman
import ExponentialDecayStructure
import ModulatedCharacters
import ModulatedCompactQuotient
import BruhatWholeQuotientStages
import ModulatedDecayCountable
import ModulatedDecayTranslations
import BruhatStageEvaluation

open Function Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

include hτ in
omit [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem modulatedKernelProjection_split (u : K) (x : ℝ) :
    modulatedKernelProjection m τ hτ (τ (Multiplicative.ofAdd x) * u.val) = u := by
  apply Subtype.ext
  change τ (Multiplicative.ofAdd x) * u.val / τ (m (τ (Multiplicative.ofAdd x) * u.val)) = u.val
  rw [map_mul,hτ,show m u.val = 1 from u.property,mul_one,mul_comm,mul_div_cancel_right]

include hτ in
/-- The angular stage's kernel is also a structural kernel of the whole split group. -/
theorem exists_splitStage_exact_kernel (hm : IsProperMap m)
    [LocallyCompactSpace (m.toMonoidHom.ker)] (p : WholeBruhatStage (m.toMonoidHom.ker)) :
    ∃ q : WholeBruhatStage G, q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype := by
  let P := p.val.1
  let N := P.kernel.map m.toMonoidHom.ker.subtype
  have hPN : N.comap m.toMonoidHom.ker.subtype = P.kernel :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective P.kernel
  have hP : IsCompact (P.kernel : Set m.toMonoidHom.ker) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  have hN : IsCompact (N : Set G) := hP.image continuous_subtype_val
  have hNm : N ≤ m.toMonoidHom.ker := by
    rintro g ⟨k, _, rfl⟩
    exact k.property
  have hGen := modulatedAnnihilator_compactlyGenerated m τ hτ N hN hNm
    (hPN.symm ▸ P.annihilator_compactlyGenerated)
  obtain ⟨J, hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hτ.surjective
  let Q : LCAStructuralPair G :=
    ⟨J, N, hN.isClosed, isOpen_lcaAnnihilator N hN, hGen, hJ ▸ le_top⟩
  obtain ⟨r⟩ := Q.quotient_elementary
  exact ⟨⟨⟨Q,r⟩,hJ⟩,rfl⟩

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H]

set_option maxHeartbeats 3500000 in
/-- The pullback of a whole-stage kernel contains a whole-stage kernel
of the modulated group. -/
theorem exists_wholeBruhatStage_kernel_le_comap (hm : IsProperMap m) (hms : Surjective m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) :
    ∃ q : WholeBruhatStage G, q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom := by
  let T := lcaAnnihilator p.val.1.kernel
  let j : T →* PontryaginDual G := (PontryaginDual.map α).toMonoidHom.comp T.subtype
  have hj : Continuous j := (PontryaginDual.map α).continuous.comp continuous_subtype_val
  obtain ⟨C,_,hC,hgen⟩ := p.val.1.annihilator_compactlyGenerated
  obtain ⟨U,hU⟩ := exists_openCompactlyGeneratedSubgroup_contains (hC.image hj)
  have hmap : Subgroup.map j ⊤ ≤ U.val := by
    rw [← hgen, MonoidHom.map_closure]
    exact (Subgroup.closure_le _).mpr hU
  obtain ⟨J,hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  let P := LCAStructuralPair.ofDual J U (show lcaDualAnnihilator U.val ≤ J.val from hJ ▸ le_top)
  obtain ⟨r⟩ := P.quotient_elementary
  let q : WholeBruhatStage G := ⟨⟨P,r⟩,hJ⟩
  refine ⟨q, fun g hg => ?_⟩
  change α g ∈ p.val.1.kernel
  rw [← lcaDualAnnihilator_annihilator p.val.1.kernel p.val.1.kernel_closed]
  apply (mem_lcaDualAnnihilator_iff T _).mpr
  intro χ
  exact (mem_lcaDualAnnihilator_iff U.val g).mp hg ⟨j χ, hmap ⟨χ, Subgroup.mem_top _, rfl⟩⟩

set_option maxHeartbeats 3500000 in
/-- A split product belongs to any stage whose kernel is compatible with
the angular factor. -/
theorem wholeBruhatDecayStage_splitProduct (hm : IsProperMap m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom)
    (I : Set ℝ) (h : p.val.Space) (f : PositiveRealExponentialDecay I) :
    ∃ v : WholeBruhatDecayStage m I q,
      ∀ g, v.val g = p.val.realize h (α g) * f.val (m g).toAdd := by
  let φ := q.coordinateMap p α hker
  let l := q.logCoordinate m
  have hl : IsProperMap l := q.logCoordinate_isProperMap m hm
  let z (g : G) := p.val.realize h (α g) * f.val (m g).toAdd
  have hmem (b : I) : modulatedExponentialWeight m b z ∈ q.val.realize.range := by
    let v : q.val.Space := ⟨_,elementarySchwartz_splitProduct_mem l hl φ.toMonoidHom.toAdditive
      (continuous_toAdd.comp (φ.continuous.comp continuous_ofAdd)) (logExponentialDecayTwist I b f) h⟩
    refine ⟨v,funext fun g => ?_⟩
    have ha : h (φ (q.coordinates g)).toAdd = p.val.realize h (α g) :=
      (congrArg (fun t => h t.toAdd) (q.coordinateMap_coordinates p α hker g)).trans
        (p.realize_eq_coordinates h (α g)).symm
    have hlog : l (q.coordinates g).toAdd = (m g).toAdd := q.logCoordinate_coordinates m g
    calc
      q.val.realize v g =
          h (φ (q.coordinates g)).toAdd * (logExponentialDecayTwist I b f) (l (q.coordinates g).toAdd) :=
        q.realize_eq_coordinates v g
      _ = p.val.realize h (α g) * ((Real.exp ((b : ℝ) * (m g).toAdd) : ℂ) * f.val (m g).toAdd) :=
        congrArg₂ (· * ·) ha (by
          rw [hlog]
          exact logExponentialDecayTwist_apply I b f (m g).toAdd)
      _ = modulatedExponentialWeight m b z g := by
        rw [modulatedExponentialWeight_apply, Complex.real_smul]
        exact mul_left_comm _ _ _
  let u : wholeBruhatDecayStageSubmodule m I q := ⟨z,(Submodule.mem_iInf _).mpr hmem⟩
  refine ⟨WholeBruhatDecayStage.algebraicEquiv.symm u,fun g => ?_⟩
  have he := (WholeBruhatDecayStage.algebraicEquiv (m := m) (I := I) (p := q)).apply_symm_apply u
  exact congrArg (fun v : wholeBruhatDecayStageSubmodule m I q => v.val g) he


omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem stageValue_injective (I : Set ℝ) (q : WholeBruhatStage G) :
    Injective (WholeBruhatDecayStage.val (m := m) (I := I) (p := q)) :=
  fun _ _ h => WholeBruhatDecayStage.algebraicEquiv.injective (Subtype.ext h)

set_option maxHeartbeats 4000000 in
/-- The split product into a compatible target stage is bilinear. -/
theorem exists_splitStageBilinear (hm : IsProperMap m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom) (I : Set ℝ) :
    ∃ B : p.val.Space →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ] WholeBruhatDecayStage m I q,
      ∀ h f g, (B h f).val g =
        p.val.realize h (α g) * f.val (m g).toAdd := by
  classical
  choose v hv using wholeBruhatDecayStage_splitProduct m hm α p q hker I
  let Y := WholeBruhatDecayStage m I q
  let R := PositiveRealExponentialDecay I
  let L (h : p.val.Space) : R →ₗ[ℂ] Y :=
    { toFun := v h
      map_add' := fun f g => stageValue_injective m I q (funext fun x => by
        change (v h (f+g)).val x = (v h f).val x + (v h g).val x
        rw [hv,hv,hv]
        exact mul_add _ _ _)
      map_smul' := fun c f => stageValue_injective m I q (funext fun x => by
        change (v h (c • f)).val x = c * (v h f).val x
        rw [hv,hv]
        exact mul_left_comm _ _ _) }
  let B : p.val.Space →ₗ[ℂ] R →ₗ[ℂ] Y :=
    { toFun := L
      map_add' := fun h h' => LinearMap.ext fun f => stageValue_injective m I q (funext fun x => by
        change (v (h+h') f).val x = (v h f).val x + (v h' f).val x
        rw [hv,hv,hv,map_add,Pi.add_apply,add_mul])
      map_smul' := fun c h => LinearMap.ext fun f => stageValue_injective m I q (funext fun x => by
        change (v (c • h) f).val x = c * (v h f).val x
        rw [hv,hv,map_smul,Pi.smul_apply,smul_eq_mul,mul_assoc]) }
  exact ⟨B,hv⟩

private theorem frechetMap_continuous_of_pointwise
    {X Y S : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y) (L : X →ₗ[ℂ] Y)
    (e : Y → S → ℂ) (he : Injective e) (hc : ∀ s, Continuous (fun y => e y s))
    (hL : ∀ s, Continuous (fun x => e (L x) s)) : Continuous L := by
  obtain ⟨haddX,hpolyX,hmetricX,hcompleteX⟩ := hX
  obtain ⟨haddY,hpolyY,hmetricY,hcompleteY⟩ := hY
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hcompleteX
  have : CompleteSpace Y := hcompleteY
  have : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  have : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  apply frechet_continuous_of_closed_graph L
  let A (s : S) : Set (X × Y) := {p | e p.2 s = e (L p.1) s}
  have hgraph : (L.graph : Set (X × Y)) = ⋂ s, A s := by
    ext p
    change p.2 = L p.1 ↔ p ∈ ⋂ s, A s
    rw [mem_iInter]
    exact ⟨fun hp s => congrFun (congrArg e hp) s,fun hp => he (funext hp)⟩
  rw [hgraph]
  exact isClosed_iInter fun s => isClosed_eq ((hc s).comp continuous_snd)
    ((hL s).comp continuous_fst)

private theorem radialDecay_continuous_eval (I : Set ℝ) (hI : I.Nonempty) (x : ℝ) :
    Continuous (fun f : PositiveRealExponentialDecay I => f.val x) := by
  obtain ⟨a,ha⟩ := hI
  let b : I := ⟨a,ha⟩
  have htwist : Continuous (fun f : PositiveRealExponentialDecay I => logExponentialDecayTwist I b f) :=
    (continuous_apply b).comp (positiveRealExponentialDecay_isEmbedding I ⟨a,ha⟩).continuous
  have heval : Continuous (fun f : 𝓢(ℝ, ℂ) => f x) :=
    (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous
  refine ((heval.comp htwist).const_smul (Real.exp (a*x))⁻¹).congr fun f => ?_
  change (Real.exp (a*x))⁻¹ • (logExponentialDecayTwist I b f x) = f.val x
  erw [logExponentialDecayTwist_apply, ← Complex.real_smul]
  exact inv_smul_smul₀ (Real.exp_ne_zero _) _

set_option maxHeartbeats 4000000 in
/-- The split product into a fixed quotient is continuous in each factor. -/
theorem exists_splitStageContinuousBilinear (hm : IsProperMap m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ B : p.val.Space →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ] WholeBruhatDecayStage m I q,
      (∀ h f g, (B h f).val g =
        p.val.realize h (α g) * f.val (m g).toAdd) ∧
      (∀ h, Continuous (B h)) ∧ (∀ f, Continuous (B.flip f)) := by
  obtain ⟨B,hB⟩ := exists_splitStageBilinear m hm α p q hker I
  have hq := (wholeBruhatDecayStage_separableNuclearFrechet m hI q).2.2
  have hR := positiveRealExponentialDecay_frechet I hInt hI
  have hp : IsFrechetTVS p.val.Space := @elementarySchwartz_frechet
    p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor
    p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete (Finite.of_fintype _)
  letI : T2Space p.val.Space := @elementarySchwartz_t2
    p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor
    p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete (Finite.of_fintype _)
  letI : T2Space (PositiveRealExponentialDecay I) :=
    (positiveRealExponentialDecay_isEmbedding I hI).t2Space
  let e := WholeBruhatDecayStage.val (m := m) (I := I) (p := q)
  have he (g : G) : Continuous (fun y => e y g) :=
    (ModulatedExponentialInductive.evaluation m I hI g).continuous.comp
      (ModulatedExponentialInductive.stageMap_continuous (m := m) (I := I) q)
  refine ⟨B,hB,fun h => ?_,fun f => ?_⟩
  · refine frechetMap_continuous_of_pointwise hR hq (B h) e
      (stageValue_injective m I q) he fun g => ?_
    exact (continuous_const.mul (radialDecay_continuous_eval I hI _)).congr fun f => (hB h f g).symm
  · refine frechetMap_continuous_of_pointwise hp hq (B.flip f) e
      (stageValue_injective m I q) he fun g => ?_
    exact ((p.val.continuous_realize_eval _).mul continuous_const).congr fun h => (hB h f g).symm

set_option maxHeartbeats 4000000 in
/-- The split product into a fixed quotient is jointly continuous, so it
defines a continuous map on the corresponding projective tensor product. -/
theorem exists_splitStageJointlyContinuous (hm : IsProperMap m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ B : p.val.Space →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ] WholeBruhatDecayStage m I q,
      (∀ h f g, (B h f).val g =
        p.val.realize h (α g) * f.val (m g).toAdd) ∧
      Continuous (fun z : p.val.Space × PositiveRealExponentialDecay I => B z.1 z.2) := by
  obtain ⟨B,hB,hR,hA⟩ := exists_splitStageContinuousBilinear m hm α p q hker I hI hInt
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  let Y := WholeBruhatDecayStage m I q
  obtain ⟨hadd,hpoly,hmetric,hcomplete⟩ : IsFrechetTVS A :=
    @elementarySchwartz_frechet p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank
      p.val.2.finiteFactor p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete
      (Finite.of_fintype _)
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace A := hcomplete
  have : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  have : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace A := BaireSpace.of_completelyPseudoMetrizable
  have : TopologicalSpace.MetrizableSpace R := (positiveRealExponentialDecay_frechet I hInt hI).choose_spec.2.1
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  exact ⟨B,hB,(bilinear_seqContinuous_of_separate B
    (fun f => (hA f).seqContinuous) (fun h => (hR h).seqContinuous)).continuous⟩

/-- Every angular stage has a common target stage for the split product. -/
theorem exists_commonSplitStage (hm : IsProperMap m) (hms : Surjective m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ (q : WholeBruhatStage G)
      (B : p.val.Space →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ] WholeBruhatDecayStage m I q),
      (∀ h f g, (B h f).val g = p.val.realize h (α g) * f.val (m g).toAdd) ∧
      Continuous (fun z : p.val.Space × PositiveRealExponentialDecay I => B z.1 z.2) := by
  obtain ⟨q, hker⟩ := exists_wholeBruhatStage_kernel_le_comap m hm hms α p
  obtain ⟨B, hB, hc⟩ := exists_splitStageJointlyContinuous m hm α p q hker I hI hInt
  exact ⟨q, B, hB, hc⟩

/-- Pointwise products intertwine left translation with the translations
in the angular and logarithmic coordinates. -/
theorem splitStageBilinear_translate (α : G →ₜ* H) (p : WholeBruhatStage H)
    (I : Set ℝ) (hI : I.Nonempty) (q : WholeBruhatStage G)
    (B : p.val.Space →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ] WholeBruhatDecayStage m I q)
    (hB : ∀ h f g, (B h f).val g = p.val.realize h (α g) * f.val (m g).toAdd)
    (h : p.val.Space) (f : PositiveRealExponentialDecay I) (g : G) :
    WholeBruhatDecayStage.translate m I q g (B h f) =
      B (elementarySchwartz_translate (p.coordinates ((α g)⁻¹)).toAdd h)
        (logExponentialDecayTranslation I hI (-(m g).toAdd) f) := by
  apply stageValue_injective m I q
  funext x
  change (B h f).val (g⁻¹ * x) =
    (B (elementarySchwartz_translate (p.coordinates ((α g)⁻¹)).toAdd h)
      (logExponentialDecayTranslation I hI (-(m g).toAdd) f)).val x
  rw [hB, hB]
  have ha : p.val.realize
      (elementarySchwartz_translate (p.coordinates ((α g)⁻¹)).toAdd h) (α x) =
      p.val.realize h (α (g⁻¹ * x)) := by
    rw [p.realize_eq_coordinates, elementarySchwartz_translate_apply, p.realize_eq_coordinates,
      map_mul α, map_inv α, mul_comm ((α g)⁻¹), map_mul]
    rfl
  rw [ha, logExponentialDecayTranslation_apply]
  congr 1
  rw [map_mul m, map_inv m]
  exact congrArg f.val (show -(m g).toAdd + (m x).toAdd = (m x).toAdd + -(m g).toAdd
    from add_comm _ _)

end

end Masullo
