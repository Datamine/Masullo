import GlobalConverseRealization
import AdelicPolarDistributions
import SLocalUnramifiedThetaRange

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open TopologicalSpace
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev B := SchwartzBergman (univ : Set ℝ)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev H := globalIdelicZetaComponentKernel F η ω
private abbrev P := (GlobalBruhat.polarEvaluation F).ker
private abbrev Q := GlobalBruhat F ⧸ H F η ω
private abbrev X := (P F).map (H F η ω).mkQ
private abbrev χ := compactIdeleClassCharacter F ω
private abbrev Z (f : GlobalBruhat F) := globalZetaContinued F ν f (χ F ω) 0

include hν in
theorem globalIdelicZetaComponentKernel_eq_homogeneous :
    H F η ω = (globalHomogeneousThetaOperator F ν ω).ker := by
  ext f
  rw [LinearMap.mem_ker]
  exact ((globalIdelicZetaKernels_eq_theta F η ν hν f).2 ω).trans
    ⟨fun h ↦ funext h, fun h z ↦ congrFun h z⟩

include hν in
theorem globalPolarFreeQuotient_isClosed : IsClosed (X F η ω : Set (Q F η ω)) := by
  by_cases ht : ω = 1
  · have hle : H F η ω ≤ P F := by
      intro f hf
      have h := (mem_globalIdelicZetaComponentKernel F η ν hν ω f).mp hf
      have hz : Z F ν ω f = 0 := funext h
      apply LinearMap.mem_ker.mpr
      apply ((globalMellin_nonneg_orders_iff F ω ν f).mp ?_).resolve_left (not_not_intro ht)
      change 0 ≤ meromorphicOrderAt (Z F ν ω f) 0 ∧ 0 ≤ meromorphicOrderAt (Z F ν ω f) 1
      rw [hz]
      change 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) 0 ∧
        0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) 1
      simp [meromorphicOrderAt_const]
    rw [← (H F η ω).isOpenQuotientMap_mkQL.isQuotientMap.isClosed_preimage]
    convert (GlobalBruhat.polarEvaluation F).isClosed_ker using 1
    ext f
    change (H F η ω).mkQ f ∈ X F η ω ↔ f ∈ P F
    constructor
    · intro hf
      obtain ⟨g, hg, he⟩ := Submodule.mem_map.mp hf
      have hfg : g - f ∈ H F η ω := (Submodule.Quotient.eq _).mp he
      exact (P F).sub_mem hg (hle hfg) |> fun h ↦ by simpa using h
    · exact fun hf ↦ Submodule.mem_map.mpr ⟨f, hf, rfl⟩
  · have hx : X F η ω = ⊤ := by
      unfold X
      rw [globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν ω]
      exact globalPolarFree_image_eq_top_of_ne_one F ν ω ht
    rw [hx, Submodule.top_coe]
    exact isClosed_univ

/-- Send a polar-free adelic test to its class in the polar-free part of
the global homogeneous theta quotient. -/
def globalPolarFreeTestClass : P F →L[ℂ] X F η ω :=
  ((H F η ω).mkQL.comp (P F).subtypeL).codRestrict _ fun f ↦
    Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩

theorem globalPolarFreeTestClass_ker :
    (globalPolarFreeTestClass F η ω).toLinearMap.ker =
      (H F η ω).comap (P F).subtype := by
  ext f
  rw [LinearMap.mem_ker]
  change (⟨(H F η ω).mkQ f.val, _⟩ : X F η ω) = 0 ↔ f.val ∈ H F η ω
  exact ⟨fun h ↦ (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h),
    fun h ↦ Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)⟩

include hν in
theorem globalPolarFreeTestClass_isOpenQuotientMap :
    IsOpenQuotientMap (globalPolarFreeTestClass F η ω) := by
  have hEq := globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν ω
  have hstrict : IsStrictMap (((H F η ω).mkQL.comp (P F).subtypeL).toLinearMap) := by
    rw [hEq]
    by_cases ht : ω = 1
    · subst ω
      exact globalHomogeneousTheta_trivial_polarFree_strict F ν
    · exact (globalHomogeneousTheta_nontrivial_polarFree_isOpenQuotientMap F ν ω ht).isQuotientMap.isStrictMap
  let L := ((H F η ω).mkQL.comp (P F).subtypeL).toLinearMap
  have hR : L.range = X F η ω := by
    change ((H F η ω).mkQ.comp (P F).subtype).range = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let e : L.range ≃ₜ X F η ω := Homeomorph.setCongr (congrArg SetLike.coe hR)
  have he : globalPolarFreeTestClass F η ω = e ∘ L.rangeRestrict := rfl
  rw [he]
  exact e.isOpenQuotientMap.comp
    (L.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hstrict)

private def continuedLinear : GlobalBruhat F →ₗ[ℂ] (ℂ → ℂ) :=
  LinearMap.pi fun z ↦ globalContinuedMellinEval F ν ω z

@[simp] private theorem continuedLinear_apply (f : GlobalBruhat F) :
    continuedLinear F ν ω f = Z F ν ω f :=
  funext (fun z ↦ globalContinuedMellinEval_apply F ν ω z f)

include hν in
/-- The global continued Mellin transform on the actual homogeneous quotient. -/
def globalQuotientMellinFunction : Q F η ω →ₗ[ℂ] (ℂ → ℂ) :=
  (H F η ω).liftQ (continuedLinear F ν ω) (by
    intro f hf
    rw [LinearMap.mem_ker, continuedLinear_apply]
    exact funext ((mem_globalIdelicZetaComponentKernel F η ν hν ω f).mp hf))

@[simp] theorem globalQuotientMellinFunction_mk (f : GlobalBruhat F) :
    globalQuotientMellinFunction F ν η hν ω ((H F η ω).mkQ f) = Z F ν ω f :=
  continuedLinear_apply F ν ω f

include hν in
theorem globalQuotientMellinFunction_injective :
    Injective (globalQuotientMellinFunction F ν η hν ω) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨f, rfl⟩ := (H F η ω).mkQ_surjective x
  rw [LinearMap.mem_ker, globalQuotientMellinFunction_mk] at hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((mem_globalIdelicZetaComponentKernel F η ν hν ω f).mpr fun z ↦ congrFun hx z)

include hν in
private theorem globalQuotientMellin_eval_continuous (z : ℂ) (hz : 1 < z.re) :
    Continuous (fun x ↦ globalQuotientMellinFunction F ν η hν ω x z) := by
  let L := idelicZetaCLM F η (χ F ω) (compactIdeleClassCharacter_unitary F ω) z hz
  have hL (f : GlobalBruhat F) : L f = Z F ν ω f z := by
    rw [idelicZetaCLM_apply]
    exact (globalZetaContinued_eq_idelic F η ν hν f (χ F ω)
      (compactIdeleClassCharacter_unitary F ω) Complex.zero_re
      (fun t ↦ by simp [χ]) z hz).symm
  let M := (H F η ω).liftQL L (by
    intro f hf
    rw [LinearMap.mem_ker]
    exact (hL f).trans ((mem_globalIdelicZetaComponentKernel F η ν hν ω f).mp hf z))
  apply M.continuous.congr
  intro x
  obtain ⟨f, rfl⟩ := (H F η ω).mkQ_surjective x
  rw [globalQuotientMellinFunction_mk]
  exact hL f

private theorem bergman_ext_of_right (b c : B)
    (h : ∀ z : ℂ, 1 < z.re → b.val z = c.val z) : b = c := by
  have hb : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  have hc : Differentiable ℂ c.val := by
    simpa only [preimage_univ, differentiableOn_univ] using c.property.2.1
  apply Subtype.ext
  funext z
  have h₂ : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by norm_num
  have hb' : AnalyticOnNhd ℂ b.val univ := fun w _ ↦ hb.analyticAt w
  have hc' : AnalyticOnNhd ℂ c.val univ := fun w _ ↦ hc.analyticAt w
  have hev : ∀ᶠ w in 𝓝 (2 : ℂ), 1 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₂
  exact (hb'.eqOn_of_preconnected_of_eventuallyEq hc' isPreconnected_univ (mem_univ (2 : ℂ))
    (hev.mono fun w hw ↦ h w hw))
    (mem_univ z)

include hν in
private theorem globalPolarFreeQuotient_bergman (x : X F η ω) :
    ∃ b : B, b.val = globalQuotientMellinFunction F ν η hν ω x.val := by
  obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp x.property
  have hv : GlobalBruhat.polarEvaluation F f = 0 := hf
  have hp : globalZetaPolarVanishes F f (χ F ω) :=
    (globalZetaPolarVanishes_compact_iff F f ω).mpr
      (Or.inr ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩)
  exact ⟨globalPoleFreeZetaBergman F ν ω f hp, by
    rw [← he, globalQuotientMellinFunction_mk]
    rfl⟩

include hν in
/-- The actual undamped Mellin transform from the polar-free part of the
global homogeneous quotient to the entire Schwartz–Bergman space. -/
def globalPolarFreeMellin : X F η ω →L[ℂ] B := by
  let M := globalQuotientMellinFunction F ν η hν ω
  let b (x : X F η ω) := (globalPolarFreeQuotient_bergman F ν η hν ω x).choose
  have hb (x : X F η ω) : (b x).val = M x.val :=
    (globalPolarFreeQuotient_bergman F ν η hν ω x).choose_spec
  let A : X F η ω →ₗ[ℂ] B :=
    { toFun := b
      map_add' := fun x y ↦ Subtype.ext (by
        change (b (x+y)).val = (b x).val + (b y).val
        rw [hb, hb, hb]
        exact map_add M x.val y.val)
      map_smul' := fun c x ↦ Subtype.ext (by
        change (b (c • x)).val = c • (b x).val
        rw [hb, hb]
        exact map_smul M c x.val) }
  have hgraph : IsClosed (A.graph : Set (X F η ω × B)) := by
    rw [show (A.graph : Set (X F η ω × B)) =
      ⋂ (z : ℂ) (hz : 1 < z.re), {p | M p.1.val z = p.2.val z} from by
        ext p
        change p ∈ A.graph ↔ _
        rw [A.mem_graph_iff]
        simp only [mem_iInter, mem_ofPred_eq]
        constructor
        · intro hp z hz
          rw [hp]
          exact (congrFun (hb p.1) z).symm
        · intro hp
          exact (bergman_ext_of_right (A p.1) p.2 fun z hz ↦
            (congrFun (hb p.1) z).trans (hp z hz)).symm]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun hz ↦ isClosed_eq
      ((globalQuotientMellin_eval_continuous F ν η hν ω z hz).comp
        (continuous_subtype_val.comp continuous_fst)) ?_
    obtain ⟨e, he⟩ := exists_schwartzBergman_jetEvaluation (I := (univ : Set ℝ))
      isOpen_univ ordConnected_univ z (mem_univ _) 0
    exact (e.continuous.comp continuous_snd).congr
      (fun p ↦ (he p.2).trans (congrFun iteratedDeriv_zero z))
  have hcont : Continuous A := by
    obtain ⟨hXa, hXp, hXm, hXc⟩ := isFrechetTVS_closedSubmodule
      (globalHomogeneousTheta_nuclearFrechet F ω η).1 (X F η ω)
      (globalPolarFreeQuotient_isClosed F ν η hν ω)
    obtain ⟨hBa, hBp, hBm, hBc⟩ := schwartzBergman_frechet _ isOpen_univ ordConnected_univ univ_nonempty
    letI : UniformSpace (X F η ω) := IsTopologicalAddGroup.rightUniformSpace _
    letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup (X F η ω) := isUniformAddGroup_of_addCommGroup
    letI : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace (X F η ω) := hXc
    letI : CompleteSpace B := hBc
    letI : MetrizableSpace (X F η ω) := hXm
    letI : MetrizableSpace B := hBm
    letI : PolynormableSpace ℂ (X F η ω) := hXp
    letI : ContinuousSMul ℂ (X F η ω) := (PolynormableSpace.withSeminorms ℂ (X F η ω)).continuousSMul
    letI : PolynormableSpace ℂ B := hBp
    letI : ContinuousSMul ℂ B := (PolynormableSpace.withSeminorms ℂ B).continuousSMul
    exact frechet_continuous_of_closed_graph A hgraph
  exact ⟨A, hcont⟩

theorem globalPolarFreeMellin_val (x : X F η ω) :
    (globalPolarFreeMellin F ν η hν ω x).val = globalQuotientMellinFunction F ν η hν ω x.val :=
  (globalPolarFreeQuotient_bergman F ν η hν ω x).choose_spec

theorem globalPolarFreeMellin_injective : Injective (globalPolarFreeMellin F ν η hν ω) := by
  intro x y he
  apply Subtype.ext
  apply globalQuotientMellinFunction_injective F ν η hν ω
  simpa only [globalPolarFreeMellin_val] using congrArg Subtype.val he

/-- A specified closed Hecke divisor ideal realizing the polar-free range
has the topology of the actual polar-free homogeneous quotient. -/
theorem globalPolarFreeMellin_equiv_of_range (r : GlobalBruhat F)
    (he : ∀ b : B, b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r) ↔
      ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Z F ν ω f = b.val) :
    ∃ e : X F η ω ≃L[ℂ] bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r),
      ∀ x, (e x).val = globalPolarFreeMellin F ν η hν ω x := by
  let D := bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r)
  let L := globalPolarFreeMellin F ν η hν ω
  let R : X F η ω →L[ℂ] D := L.codRestrict D (by
    intro x
    apply (he (L x)).mpr
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    refine ⟨f, hf, ?_⟩
    rw [globalPolarFreeMellin_val, ← hfx, globalQuotientMellinFunction_mk])
  have hsurj : Surjective R := by
    intro b
    obtain ⟨f, hf, hfb⟩ := (he b.val).mp b.property
    let x : X F η ω := ⟨(H F η ω).mkQ f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩
    refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
    change (L x).val = b.val.val
    rw [globalPolarFreeMellin_val]
    exact (globalQuotientMellinFunction_mk F ν η hν ω f).trans hfb
  have hinj : Injective R := fun _ _ h ↦
    globalPolarFreeMellin_injective F ν η hν ω (congrArg Subtype.val h)
  have hD : IsClosed (D : Set B) := bergmanDivisorSubmodule_isClosed
    (fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt)
  have hOpen : IsOpenMap R := by
    obtain ⟨hXa, hXp, hXm, hXc⟩ := isFrechetTVS_closedSubmodule
      (globalHomogeneousTheta_nuclearFrechet F ω η).1 (X F η ω)
      (globalPolarFreeQuotient_isClosed F ν η hν ω)
    obtain ⟨hDa, hDp, hDm, hDc⟩ := isFrechetTVS_closedSubmodule
      (schwartzBergman_frechet _ isOpen_univ ordConnected_univ univ_nonempty) D hD
    letI : UniformSpace (X F η ω) := IsTopologicalAddGroup.rightUniformSpace _
    letI : CompleteSpace (X F η ω) := hXc
    letI : MetrizableSpace (X F η ω) := hXm
    letI : PolynormableSpace ℂ (X F η ω) := hXp
    letI : ContinuousSMul ℂ (X F η ω) := (PolynormableSpace.withSeminorms ℂ (X F η ω)).continuousSMul
    letI : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace D := hDc
    letI : MetrizableSpace D := hDm
    letI : PolynormableSpace ℂ D := hDp
    letI : ContinuousSMul ℂ D := (PolynormableSpace.withSeminorms ℂ D).continuousSMul
    letI : (uniformity D).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    letI : BaireSpace D := BaireSpace.of_completelyPseudoMetrizable
    exact isOpenMap_of_surjective_complete_baire R hsurj
  let E := LinearEquiv.ofBijective R.toLinearMap ⟨hinj, hsurj⟩
  let e := E.toEquiv.toHomeomorphOfContinuousOpen R.continuous hOpen
  exact ⟨⟨E, e.continuous_toFun, e.symm.continuous_toFun⟩, fun _ ↦ rfl⟩

/-- Translation carries a specified topological Mellin equivalence to its
shifted divisor ideal. -/
theorem globalPolarFreeMellin_shift_equiv_of_equiv (r : GlobalBruhat F)
    (e : X F η ω ≃L[ℂ] bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r))
    (he : ∀ x, (e x).val = globalPolarFreeMellin F ν η hν ω x) (d : ℂ) :
    ∃ E : X F η ω ≃L[ℂ]
        bergmanDivisorSubmodule (fun z ↦ globalHeckeClearedZeta F ν ω r (z + d)),
      ∀ f : P F, ∀ z : ℂ,
        (E (globalPolarFreeTestClass F η ω f)).val.val z = Z F ν ω f.val (z + d) := by
  let g := globalHeckeClearedZeta F ν ω r
  have hg : Differentiable ℂ g := fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  let D := bergmanDivisorSubmodule g
  let D' := bergmanDivisorSubmodule (fun z ↦ g (z + d))
  let s := schwartzBergmanEntireShift d
  let A : D →L[ℂ] D' := (s.toContinuousLinearMap.comp D.subtypeL).codRestrict D'
    fun b ↦ (bergmanDivisorSubmodule_shift_mem_iff hg d b.val).mpr b.property
  let C : D' →L[ℂ] D := (s.symm.toContinuousLinearMap.comp D'.subtypeL).codRestrict D
    fun b ↦ (bergmanDivisorSubmodule_shift_mem_iff hg d (s.symm b.val)).mp (by
      change s (s.symm b.val) ∈ D'
      rw [s.apply_symm_apply]
      exact b.property)
  let S : D ≃L[ℂ] D' := ContinuousLinearEquiv.equivOfInverse A C
    (fun b ↦ Subtype.ext (s.symm_apply_apply b.val))
    (fun b ↦ Subtype.ext (s.apply_symm_apply b.val))
  refine ⟨e.trans S, fun f z ↦ ?_⟩
  change (s (e (globalPolarFreeTestClass F η ω f)).val).val z = _
  rw [schwartzBergmanEntireShift_apply, he, globalPolarFreeMellin_val]
  exact congrFun (globalQuotientMellinFunction_mk F ν η hν ω f.val) (z + d)

section Divisor

variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

include μ in
/-- The global polar-free Mellin transform is a continuous linear
isomorphism onto the closed Hecke divisor subspace with its induced topology. -/
theorem exists_globalPolarFreeMellin_equiv :
    ∃ r : GlobalBruhat F,
      (∀ z, analyticOrderAt (globalHeckeClearedZeta F ν ω r) z ≠ ⊤) ∧
      ∃ e : X F η ω ≃L[ℂ] bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r),
        ∀ x, (e x).val = globalPolarFreeMellin F ν η hν ω x := by
  obtain ⟨r, _, hr, _, he⟩ := exists_globalHeckeDivisor_polarFree_range F ν η μ hν ω
  exact ⟨r, hr, globalPolarFreeMellin_equiv_of_range F ν η hν ω r he⟩

include μ hν in
/-- The same topological isomorphism in the chart obtained by translating
the spectral parameter. Its action on actual tests is the shifted zeta integral. -/
theorem exists_globalPolarFreeMellin_shift_equiv (d : ℂ) :
    ∃ r : GlobalBruhat F,
      (∀ z, analyticOrderAt (globalHeckeClearedZeta F ν ω r) z ≠ ⊤) ∧
      ∃ e : X F η ω ≃L[ℂ]
          bergmanDivisorSubmodule (fun z ↦ globalHeckeClearedZeta F ν ω r (z + d)),
        ∀ f : P F, ∀ z : ℂ,
          (e (globalPolarFreeTestClass F η ω f)).val.val z = Z F ν ω f.val (z + d) := by
  obtain ⟨r, hr, e, he⟩ := exists_globalPolarFreeMellin_equiv F ν η hν ω μ
  exact ⟨r, hr, globalPolarFreeMellin_shift_equiv_of_equiv F ν η hν ω r e he d⟩

end Divisor

/-- Points in a shifted Mellin chart away from the two possible poles. -/
def globalShiftedMellinRegularSet (d : ℂ) : Set ℂ :=
  {z | z + d ≠ 0 ∧ z + d ≠ 1}

include hν in
/-- The continued Mellin function on the regular part of a shifted chart. -/
def globalRegularMellin (d : ℂ) :
    Q F η ω →ₗ[ℂ] (globalShiftedMellinRegularSet d → ℂ) :=
  LinearMap.pi fun z ↦ (LinearMap.proj (z.val + d)).comp
    (globalQuotientMellinFunction F ν η hν ω)

@[simp] theorem globalRegularMellin_mk_apply (d : ℂ) (f : GlobalBruhat F)
    (z : globalShiftedMellinRegularSet d) :
    globalRegularMellin F ν η hν ω d ((H F η ω).mkQ f) z = Z F ν ω f (z.val + d) :=
  congrFun (globalQuotientMellinFunction_mk F ν η hν ω f) (z.val + d)

private theorem shiftedMellin_regular_eventually (d a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, z ∈ globalShiftedMellinRegularSet d := by
  have hne (w : ℂ) : ∀ᶠ z in 𝓝[≠] a, z ≠ w := by
    rcases eq_or_ne a w with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hne (-d), hne (1 - d)] with z hz₀ hz₁
  exact ⟨fun h ↦ hz₀ (eq_neg_of_add_eq_zero_left h), fun h ↦ hz₁ (eq_sub_of_add_eq h)⟩

include hν in
theorem globalRegularMellin_injective (d : ℂ) :
    Injective (globalRegularMellin F ν η hν ω d) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨f, rfl⟩ := (H F η ω).mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  simp only [H, globalIdelicZetaComponentKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y
  let w : ℂ := 2 + (y : ℂ) * Complex.I
  have hwr : w.re = 2 := by simp [w]
  have hw : 1 < w.re := by rw [hwr]; norm_num
  have hw₀ : w ≠ 0 := fun h ↦ by rw [h] at hwr; norm_num at hwr
  have hw₁ : w ≠ 1 := fun h ↦ by rw [h] at hwr; norm_num at hwr
  let z : globalShiftedMellinRegularSet d := ⟨w - d, by
    change w - d + d ≠ 0 ∧ w - d + d ≠ 1
    rw [sub_add_cancel]
    exact ⟨hw₀, hw₁⟩⟩
  have he := congrFun (LinearMap.mem_ker.mp hx) z
  change globalQuotientMellinFunction F ν η hν ω ((H F η ω).mkQ f) (w - d + d) = 0 at he
  rw [sub_add_cancel, globalQuotientMellinFunction_mk] at he
  change idelicZetaCLM F η (χ F ω) (compactIdeleClassCharacter_unitary F ω) w hw f = 0
  rw [idelicZetaCLM_apply, ← globalZetaContinued_eq_idelic F η ν hν f (χ F ω)
    (compactIdeleClassCharacter_unitary F ω) Complex.zero_re (fun t ↦ by simp [χ]) w hw]
  exact he

include hν in
/-- The residue sequence remains strict on the meromorphic Mellin image
when that image carries the quotient topology stipulated in the manuscript. -/
theorem globalTrivialMellin_regular_residue_exact (d : ℂ) :
    let M := globalRegularMellin F ν η hν (1 : PontryaginDual (K F)) d
    letI : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
    ∃ R : M.range →ₗ[ℂ] ℂ × ℂ,
      IsHomeomorph M.rangeRestrict ∧
      R.ker = (X F η 1).map M.rangeRestrict ∧
      IsOpenQuotientMap R ∧
      IsClosedEmbedding (M.rangeRestrict.comp (X F η 1).subtype) ∧
      (∀ f : GlobalBruhat F,
        R (M.rangeRestrict ((H F η 1).mkQ f)) =
          (-((ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).1),
            (ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).2)) ∧
      ∀ (b : M.range) (g : ℂ → ℂ), (∀ z : globalShiftedMellinRegularSet d, g z.val = b.val z) →
        Tendsto (fun z ↦ (z - (-d)) * g z) (𝓝[≠] (-d)) (𝓝 (R b).1) ∧
        Tendsto (fun z ↦ (z - (1 - d)) * g z) (𝓝[≠] (1 - d)) (𝓝 (R b).2) := by
  intro M
  letI : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
  have hkernel := globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν
    (1 : PontryaginDual (K F))
  have hres := globalHomogeneousTheta_trivial_residue_exact F ν
  rw [← hkernel] at hres
  obtain ⟨R₀, _, hR₀ker, hR₀open, _, hR₀⟩ := hres
  let i := LinearEquiv.ofInjective M (globalRegularMellin_injective F ν η hν 1 d)
  have hi : IsHomeomorph M.rangeRestrict := isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨⟨⟨rfl⟩, M.surjective_rangeRestrict⟩, i.injective⟩
  have hinv : Continuous i.symm := hi.isQuotientMap.continuous_iff.mpr (by
    change Continuous (fun x ↦ i.symm (i x))
    simpa only [LinearEquiv.symm_apply_apply, Function.id_def] using (continuous_id : Continuous (id : Q F η 1 → Q F η 1)))
  have hiopen : IsOpenQuotientMap i.symm := ⟨i.symm.surjective, hinv, fun U hU ↦ by
    rw [i.symm.image_eq_preimage_symm]
    exact hi.continuous.isOpen_preimage U hU⟩
  let R := R₀.toLinearMap.comp i.symm.toLinearMap
  have hR (x : Q F η 1) : R (M.rangeRestrict x) = R₀ x :=
    congrArg R₀ (i.symm_apply_apply x)
  refine ⟨R, hi, ?_, hR₀open.comp hiopen, ?_, fun f ↦ (hR _).trans (hR₀ f).1, ?_⟩
  · ext b
    obtain ⟨x, rfl⟩ := M.surjective_rangeRestrict b
    change R (M.rangeRestrict x) = 0 ↔ _
    rw [hR]
    change x ∈ R₀.toLinearMap.ker ↔ _
    rw [hR₀ker]
    exact ⟨fun hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩, fun h ↦ by
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp h
      exact i.injective he ▸ hy⟩
  · exact hi.isClosedEmbedding.comp
      (globalPolarFreeQuotient_isClosed F ν η hν 1).isClosedEmbedding_subtypeVal
  · intro b g hg
    obtain ⟨x, rfl⟩ := M.surjective_rangeRestrict b
    obtain ⟨f, rfl⟩ := (H F η 1).mkQ_surjective x
    rw [hR]
    have ht (a : ℂ) : Tendsto (fun z : ℂ ↦ z + d) (𝓝[≠] (a - d)) (𝓝[≠] a) := by
      rw [Tendsto, Filter.map_add_right_nhdsNE, sub_add_cancel]
    have h₀ := (globalZetaContinued_trivial_residues F ν f).1.comp (ht 0)
    have h₁ := (globalZetaContinued_trivial_residues F ν f).2.comp (ht 1)
    rw [(hR₀ f).1]
    refine ⟨?_, ?_⟩
    · have h₀' : Tendsto (fun z ↦ (z + d) * Z F ν 1 f (z + d)) (𝓝[≠] (-d))
          (𝓝 (-((ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f).val 0))) := by
        simpa only [Function.comp_def, zero_sub] using h₀
      apply h₀'.congr'
      filter_upwards [shiftedMellin_regular_eventually d (-d)] with z hz
      rw [hg ⟨z, hz⟩]
      change (z + d) * Z F ν 1 f (z + d) =
        (z - -d) * globalRegularMellin F ν η hν 1 d ((H F η 1).mkQ f) ⟨z, hz⟩
      rw [globalRegularMellin_mk_apply, sub_neg_eq_add]
    · apply h₁.congr'
      filter_upwards [shiftedMellin_regular_eventually d (1 - d)] with z hz
      rw [hg ⟨z, hz⟩]
      change ((z + d) - 1) * Z F ν 1 f (z + d) =
        (z - (1 - d)) * globalRegularMellin F ν η hν 1 d ((H F η 1).mkQ f) ⟨z, hz⟩
      rw [globalRegularMellin_mk_apply, sub_sub_eq_add_sub]

#print axioms globalPolarFreeTestClass_ker
#print axioms globalPolarFreeTestClass_isOpenQuotientMap
#print axioms globalPolarFreeMellin
#print axioms globalPolarFreeMellin_injective
#print axioms exists_globalPolarFreeMellin_equiv
#print axioms exists_globalPolarFreeMellin_shift_equiv
#print axioms globalTrivialMellin_regular_residue_exact

end

end Masullo
