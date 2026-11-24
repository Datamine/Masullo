import GlobalPrincipalValueConverse

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
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

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev H := globalIdelicZetaComponentKernel F η ω
private abbrev Q := GlobalBruhat F ⧸ H F η ω
private abbrev A := (GlobalBruhat.polarEvaluation F).ker
private abbrev X := (A F).map (H F η ω).mkQ
private abbrev V (W : Finset (Place F)) := globalHomogeneousPrincipalValues F ν η μ hν ω W
private abbrev Z (f : GlobalBruhat F) := globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0
private abbrev G (f : GlobalBruhat F) := globalHeckeClearedZeta F ν ω f
private abbrev P := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω)
private abbrev generator (W : Finset (Place F)) (r : GlobalBruhat F) (z : ℂ) :=
  P F ω W z * G F ν ω r z

include μ hν in
/-- The principal-value Mellin transform on the regular part of a shifted chart. -/
def globalRegularPrincipalMellin (W : Finset (Place F)) (d : ℂ) :
    Q F η ω →ₗ[ℂ] (globalShiftedMellinRegularSet d → ℂ) :=
  (globalRegularMellin F ν η hν ω d).comp (V F ν η μ hν ω W).toLinearMap

@[simp] theorem globalRegularPrincipalMellin_mk (W : Finset (Place F)) (d : ℂ)
    (f : GlobalBruhat F) (z : globalShiftedMellinRegularSet d) :
    globalRegularPrincipalMellin F ν η μ hν ω W d ((H F η ω).mkQ f) z =
      Z F ν ω (globalWeilPrincipalValues F W f) (z.val + d) := by
  change globalRegularMellin F ν η hν ω d (V F ν η μ hν ω W ((H F η ω).mkQ f)) z = _
  rw [globalHomogeneousPrincipalValues_mk, globalRegularMellin_mk_apply]

theorem globalRegularPrincipalMellin_injective (W : Finset (Place F)) (d : ℂ) :
    Injective (globalRegularPrincipalMellin F ν η μ hν ω W d) :=
  (globalRegularMellin_injective F ν η hν ω d).comp
    (globalHomogeneousPrincipalValues_injective F ν η μ hν ω W)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem generator_differentiable (W : Finset (Place F)) (r : GlobalBruhat F) :
    Differentiable ℂ (generator F ν ω W r) := by
  have hp : Differentiable ℂ (P F ω W) := fun z ↦
    (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).differentiableAt
  have hg : Differentiable ℂ (G F ν ω r) := fun z ↦
    (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  exact hp.mul hg

private theorem divisorShift_equiv {g : ℂ → ℂ} (hg : Differentiable ℂ g) (d : ℂ) :
    ∃ s : bergmanDivisorSubmodule g ≃L[ℂ] bergmanDivisorSubmodule (fun z ↦ g (z + d)),
      ∀ b, (s b).val = schwartzBergmanEntireShift d b.val := by
  let D := bergmanDivisorSubmodule g
  let E := bergmanDivisorSubmodule (fun z ↦ g (z + d))
  let S := schwartzBergmanEntireShift d
  let L : D →L[ℂ] E := (S.toContinuousLinearMap.comp D.subtypeL).codRestrict E
    fun b ↦ (bergmanDivisorSubmodule_shift_mem_iff hg d b.val).mpr b.property
  let R : E →L[ℂ] D := (S.symm.toContinuousLinearMap.comp E.subtypeL).codRestrict D
    fun b ↦ (bergmanDivisorSubmodule_shift_mem_iff hg d (S.symm b.val)).mp (by
      change S (S.symm b.val) ∈ E
      rw [S.apply_symm_apply]
      exact b.property)
  exact ⟨ContinuousLinearEquiv.equivOfInverse L R
    (fun b ↦ Subtype.ext (S.symm_apply_apply b.val))
    (fun b ↦ Subtype.ext (S.apply_symm_apply b.val)), fun _ ↦ rfl⟩

include μ hν in
/-- The polar-free principal-value Mellin chart is a topological equivalence
onto the shifted completed divisor ideal with the selected Euler factors. -/
theorem exists_globalPV_polarFree_shift_equiv_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (W : Finset (Place F)) (d : ℂ) :
    ∃ e : X F η ω ≃L[ℂ] bergmanDivisorSubmodule (fun z ↦ generator F ν ω W r (z + d)),
      ∀ f : A F, ∀ z : ℂ,
        (e (globalPolarFreeTestClass F η ω f)).val.val z =
          Z F ν ω (globalWeilPrincipalValues F W f.val) (z + d) := by
  obtain ⟨e, he⟩ := exists_globalPV_polarFree_equiv_of_min F ν η μ hν ω r hr hmin W
  obtain ⟨s, hs⟩ := divisorShift_equiv (generator_differentiable F ν ω W r) d
  refine ⟨e.trans s, fun f z ↦ ?_⟩
  change (s (e (globalPolarFreeTestClass F η ω f))).val.val z = _
  rw [hs, schwartzBergmanEntireShift_apply, he]

include μ hν in
/-- The full trivial principal-value middle term in a shifted chart is
determined by the pole-polynomial multiple in the selected divisor ideal. -/
theorem globalRegularPrincipalMellin_trivial_range_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν 1 r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν 1 r) z ≤ meromorphicOrderAt (Z F ν 1 f) z)
    (W : Finset (Place F)) (d : ℂ) :
    let M := globalRegularPrincipalMellin F ν η μ hν 1 W d
    ∀ u : globalShiftedMellinRegularSet d → ℂ, u ∈ M.range ↔
      ∃ b : B, b ∈ bergmanDivisorSubmodule (fun z ↦ generator F ν 1 W r (z + d)) ∧
        ∀ z : globalShiftedMellinRegularSet d,
          b.val z.val = (z.val + d) * (1 - z.val - d) * u z := by
  intro M u
  let S := schwartzBergmanEntireShift d
  have hRange := globalPV_trivial_cleared_divisor_range_of_min F ν η μ hν r hr hmin W
  have hShift (b : B) :
      S b ∈ bergmanDivisorSubmodule (fun z ↦ generator F ν 1 W r (z + d)) ↔
        b ∈ bergmanDivisorSubmodule (generator F ν 1 W r) :=
    bergmanDivisorSubmodule_shift_mem_iff (generator_differentiable F ν 1 W r) d b
  have hTest (f : GlobalBruhat F) (z : globalShiftedMellinRegularSet d) :
      G F ν 1 (globalWeilPrincipalValues F W f) (z.val + d) =
        (z.val + d) * (1 - z.val - d) * M ((H F η 1).mkQ f) z := by
    change globalHeckeClearedZeta F ν 1 _ (z.val + d) = _
    rw [globalHeckeClearedZeta_eq F ν 1 _ _ z.property.1 z.property.2]
    change _ = _ * globalRegularPrincipalMellin F ν η μ hν 1 W d ((H F η 1).mkQ f) z
    rw [globalRegularPrincipalMellin_mk]
    simp only [globalHeckePoleFactor, ite_true]
    ring
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := (H F η 1).mkQ_surjective x
    let b : B := ⟨G F ν 1 (globalWeilPrincipalValues F W f),
      globalTrivialClearedZeta_mem_schwartzBergman F ν η hν _⟩
    refine ⟨S b, (hShift b).mpr ((hRange b).mpr ⟨f, rfl⟩), fun z ↦ ?_⟩
    change (schwartzBergmanEntireShift d b).val z.val = _
    rw [schwartzBergmanEntireShift_apply]
    exact hTest f z
  · rintro ⟨b, hb, he⟩
    let a := S.symm b
    have ha : S a = b := S.apply_symm_apply b
    obtain ⟨f, hf⟩ := (hRange a).mp ((hShift a).mp (ha.symm ▸ hb))
    refine ⟨(H F η 1).mkQ f, funext fun z ↦ ?_⟩
    have h₁ : 1 - z.val - d ≠ 0 := by
      rw [← sub_add_eq_sub_sub]
      exact sub_ne_zero.mpr z.property.2.symm
    apply mul_left_cancel₀ (mul_ne_zero z.property.1 h₁)
    have hf' : G F ν 1 (globalWeilPrincipalValues F W f) = a.val := hf
    rw [← hTest, hf', ← he, ← ha, schwartzBergmanEntireShift_apply]

private theorem regular_eventually (d a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, z ∈ globalShiftedMellinRegularSet d := by
  have hn (w : ℂ) : ∀ᶠ z in 𝓝[≠] a, z ≠ w := by
    rcases eq_or_ne a w with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hn (-d), hn (1-d)] with z h₀ h₁
  exact ⟨fun h ↦ h₀ (eq_neg_of_add_eq_zero_left h), fun h ↦ h₁ (eq_sub_of_add_eq h)⟩

private theorem embeddedRange_equiv {E Y : Type*}
    [AddCommGroup E] [AddCommGroup Y] [Module ℂ E] [Module ℂ Y]
    [TopologicalSpace E] [TopologicalSpace Y]
    (L : E →L[ℂ] Y) (hL : IsEmbedding L) :
    ∃ e : E ≃L[ℂ] L.toLinearMap.range, ∀ x, e x = L.rangeRestrict x := by
  let i := LinearEquiv.ofInjective L.toLinearMap hL.injective
  have h : IsHomeomorph L.rangeRestrict := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨IsEmbedding.subtypeVal.of_comp_iff.mp hL, L.toLinearMap.surjective_rangeRestrict⟩
  have hinv : Continuous i.symm := h.isQuotientMap.continuous_iff.mpr (by
    change Continuous (fun x ↦ i.symm (i x))
    simpa only [LinearEquiv.symm_apply_apply, Function.id_def] using
      (continuous_id : Continuous (id : E → E)))
  exact ⟨⟨i, h.continuous, hinv⟩, fun _ ↦ rfl⟩

set_option maxHeartbeats 1000000 in
include μ hν in
/-- The corrected strict sequence on the trivial meromorphic principal-value
image uses the residues after division by the selected Euler multiplier. The
Mellin image topology is the quotient topology of the actual adelic image. -/
theorem globalTrivialPrincipalMellin_residue_exact (W : Finset (Place F)) (d : ℂ) :
    let U := V F ν η μ hν 1 W
    let M := globalRegularPrincipalMellin F ν η μ hν 1 W d
    letI : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
    ∃ (E : U.toLinearMap.range ≃L[ℂ] M.range) (R : M.range →ₗ[ℂ] ℂ × ℂ),
      (∀ x, E (U.rangeRestrict x) = M.rangeRestrict x) ∧
      IsHomeomorph M.rangeRestrict ∧
      R.ker = (X F η 1).map M.rangeRestrict ∧
      (R.comp E.toLinearMap).ker = (X F η 1).map U.rangeRestrict.toLinearMap ∧
      IsOpenQuotientMap R ∧ IsOpenQuotientMap (R.comp E.toLinearMap) ∧
      IsClosedEmbedding (M.rangeRestrict.comp (X F η 1).subtype) ∧
      IsClosedEmbedding (U.rangeRestrict.toLinearMap.comp (X F η 1).subtype) ∧
      (∀ f : GlobalBruhat F,
        R (M.rangeRestrict ((H F η 1).mkQ f)) =
          (-((ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).1),
            (ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).2)) ∧
      ∀ (b : M.range) (g : ℂ → ℂ), (∀ z : globalShiftedMellinRegularSet d, g z.val = b.val z) →
        let recover (z : ℂ) := g z / P F 1 W (z + d)
        Tendsto (fun z ↦ (z - (-d)) * recover z) (𝓝[≠] (-d)) (𝓝 (R b).1) ∧
        Tendsto (fun z ↦ (z - (1-d)) * recover z) (𝓝[≠] (1-d)) (𝓝 (R b).2) := by
  intro U M
  letI : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
  have hKernel : H F η (1 : PontryaginDual (K F)) = (globalHomogeneousThetaOperator F ν 1).ker :=
    globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν 1
  have hres := globalHomogeneousTheta_trivial_residue_exact F ν
  rw [← hKernel] at hres
  obtain ⟨R₀, _, hR₀ker, hR₀open, _, hR₀⟩ := hres
  let i := LinearEquiv.ofInjective M (globalRegularPrincipalMellin_injective F ν η μ hν 1 W d)
  have hi : IsHomeomorph M.rangeRestrict := isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨⟨⟨rfl⟩, M.surjective_rangeRestrict⟩, i.injective⟩
  have hinv : Continuous i.symm := hi.isQuotientMap.continuous_iff.mpr (by
    change Continuous (fun x ↦ i.symm (i x))
    simpa only [LinearEquiv.symm_apply_apply, Function.id_def] using
      (continuous_id : Continuous (id : Q F η 1 → Q F η 1)))
  let I : Q F η 1 ≃L[ℂ] M.range := ⟨i, hi.continuous, hinv⟩
  obtain ⟨J, hJ⟩ := embeddedRange_equiv U
    (globalHomogeneousPrincipalValues_isClosedEmbedding F ν η μ hν 1 W).isEmbedding
  have hJFun : (J : Q F η 1 → U.toLinearMap.range) = U.rangeRestrict := funext hJ
  have hj : IsHomeomorph U.rangeRestrict := hJFun ▸ J.toHomeomorph.isHomeomorph
  let E := J.symm.trans I
  let R := R₀.toLinearMap.comp i.symm.toLinearMap
  have hE (x : Q F η 1) : E (U.rangeRestrict x) = M.rangeRestrict x := by
    change I (J.symm (U.rangeRestrict x)) = I x
    rw [← hJ, J.symm_apply_apply]
  have hR (x : Q F η 1) : R (M.rangeRestrict x) = R₀ x :=
    congrArg R₀ (i.symm_apply_apply x)
  have hopen : IsOpenQuotientMap R := hR₀open.comp I.symm.toHomeomorph.isOpenQuotientMap
  refine ⟨E, R, hE, hi, ?_, ?_, hopen, hopen.comp E.toHomeomorph.isOpenQuotientMap, ?_, ?_,
    fun f ↦ (hR _).trans (hR₀ f).1, ?_⟩
  · apply Submodule.ext
    intro b
    obtain ⟨x, rfl⟩ := M.surjective_rangeRestrict b
    change R (M.rangeRestrict x) = 0 ↔ _
    rw [hR]
    change x ∈ R₀.toLinearMap.ker ↔ _
    rw [hR₀ker]
    exact ⟨fun hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩, fun h ↦ by
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp h
      exact i.injective he ▸ hy⟩
  · apply Submodule.ext
    intro b
    let x := J.symm b
    have hx' : U.rangeRestrict x = b := (hJ x).symm.trans (J.apply_symm_apply b)
    rw [← hx']
    have hVal : R (E (U.rangeRestrict x)) = R₀ x :=
      (congrArg (fun w : M.range ↦ R w) (hE x)).trans (hR x)
    have hLeft : R (E (U.rangeRestrict x)) = 0 ↔ x ∈ X F η 1 :=
      (Iff.of_eq (congrArg (· = 0) hVal)).trans
        ((LinearMap.mem_ker (f := R₀.toLinearMap)).symm.trans
          (Iff.of_eq (congrArg (fun S : Submodule ℂ (Q F η 1) ↦ x ∈ S) hR₀ker)))
    change (R (E (U.rangeRestrict x)) = 0) ↔ U.rangeRestrict x ∈
      (X F η 1).map U.rangeRestrict.toLinearMap
    exact hLeft.trans ⟨fun hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩, fun h ↦ by
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp h
      exact hj.injective he ▸ hy⟩
  · exact hi.isClosedEmbedding.comp
      (globalPolarFreeQuotient_isClosed F ν η hν 1).isClosedEmbedding_subtypeVal
  · exact hj.isClosedEmbedding.comp
      (globalPolarFreeQuotient_isClosed F ν η hν 1).isClosedEmbedding_subtypeVal
  · intro b g hg recover
    obtain ⟨x, rfl⟩ := M.surjective_rangeRestrict b
    obtain ⟨f, rfl⟩ := (H F η 1).mkQ_surjective x
    rw [hR, (hR₀ f).1]
    have ht (a : ℂ) : Tendsto (fun z : ℂ ↦ z + d) (𝓝[≠] (a-d)) (𝓝[≠] a) := by
      rw [Tendsto, Filter.map_add_right_nhdsNE, sub_add_cancel]
    let v (z : ℂ) := Z F ν 1 (globalWeilPrincipalValues F W f) z / P F 1 W z
    have hv (a : ℂ) : (fun z ↦ v (z + d)) =ᶠ[𝓝[≠] a] recover := by
      filter_upwards [regular_eventually d a] with z hz
      have h := hg ⟨z,hz⟩
      change g z = globalRegularPrincipalMellin F ν η μ hν 1 W d ((H F η 1).mkQ f) ⟨z,hz⟩ at h
      rw [globalRegularPrincipalMellin_mk] at h
      change _ = g z / P F 1 W (z+d)
      rw [h]
    have h₀ := (globalPV_trivial_recovered_residues F ν η μ hν W f).1.comp (ht 0)
    have h₁ := (globalPV_trivial_recovered_residues F ν η μ hν W f).2.comp (ht 1)
    refine ⟨?_, ?_⟩
    · have h₀' : Tendsto (fun z ↦ (z+d) * v (z+d)) (𝓝[≠] (-d))
          (𝓝 (-((ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).1))) := by
        simpa only [Function.comp_def, zero_sub] using h₀
      exact h₀'.congr' ((hv (-d)).mono fun z hz ↦ by
        change (z+d) * v (z+d) = (z - -d) * recover z
        rw [sub_neg_eq_add]
        exact congrArg ((z+d) * ·) hz)
    · exact h₁.congr' ((hv (1-d)).mono fun z hz ↦ by
        change (z+d-1) * v (z+d) = (z - (1-d)) * recover z
        rw [sub_sub_eq_add_sub]
        exact congrArg ((z+d-1) * ·) hz)

private abbrev polarPrincipalTests (W : Finset (Place F)) : A F →L[ℂ] GlobalBruhat F :=
  (globalWeilPrincipalValues F W).comp (A F).subtypeL

include μ hν in
/-- The shifted Mellin map from the actual principal-value polar-free tests
is open onto the closed divisor ideal. Its kernel is the principal-value
image of the input theta kernel intersected with the polar-free tests. -/
theorem exists_globalPV_test_shift_map_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (W : Finset (Place F)) (d : ℂ) :
    let U := polarPrincipalTests F W
    let D := bergmanDivisorSubmodule (fun z ↦ generator F ν ω W r (z + d))
    ∃ L : U.toLinearMap.range →L[ℂ] D,
      IsOpenQuotientMap L ∧
      L.toLinearMap.ker = ((H F η ω).comap (A F).subtype).map U.rangeRestrict.toLinearMap ∧
      ∀ f : U.toLinearMap.range, ∀ z : ℂ, (L f).val.val z = Z F ν ω f.val (z + d) := by
  intro U D
  obtain ⟨J, hJ⟩ := embeddedRange_equiv U
    ((globalWeilPrincipalValues_closedEmbedding F W).isEmbedding.comp IsEmbedding.subtypeVal)
  obtain ⟨e, he⟩ := exists_globalPV_polarFree_shift_equiv_of_min F ν η μ hν ω r hr hmin W d
  let A₀ := globalPolarFreeTestClass F η ω
  let L : U.toLinearMap.range →L[ℂ] D :=
    e.toContinuousLinearMap.comp (A₀.comp J.symm.toContinuousLinearMap)
  have hL (x : A F) : L (J x) = e (A₀ x) := by
    change e (A₀ (J.symm (J x))) = e (A₀ x)
    rw [J.symm_apply_apply]
  refine ⟨L, ?_, ?_, ?_⟩
  · exact e.toHomeomorph.isOpenQuotientMap.comp
      ((globalPolarFreeTestClass_isOpenQuotientMap F ν η hν ω).comp J.symm.toHomeomorph.isOpenQuotientMap)
  · apply Submodule.ext
    intro y
    obtain ⟨x, rfl⟩ := J.surjective y
    rw [LinearMap.mem_ker]
    change L (J x) = 0 ↔ _
    rw [hL, map_eq_zero_iff e e.injective, hJ]
    change x ∈ A₀.toLinearMap.ker ↔ _
    rw [globalPolarFreeTestClass_ker]
    constructor
    · exact fun hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    · intro h
      obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp h
      have he' : U.rangeRestrict u = U.rangeRestrict x := heq
      rw [← hJ u, ← hJ x] at he'
      exact J.injective he' ▸ hu
  · intro y z
    obtain ⟨x, rfl⟩ := J.surjective y
    rw [hL, hJ]
    exact he x z

set_option maxHeartbeats 700000 in
include μ hν in
/-- For a nontrivial character the Mellin map from the full actual
homogeneous principal-value image is the shifted closed Euler divisor
ideal with the Schwartz–Bergman subspace topology. -/
theorem exists_globalPV_nontrivial_shift_converse
    (hω : ω ≠ 1) (W : Finset (Place F)) (d : ℂ) :
    let U := V F ν η μ hν ω W
    ∃ (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (r : GlobalBruhat F) (C : ℂ), C ≠ 0 ∧
      EqOn (Z F ν ω r) (fun z ↦ C * globalCompletedHeckeEuler F ω S hS hu z) {z | 1 < z.re} ∧
      ∃ e : U.toLinearMap.range ≃L[ℂ] bergmanDivisorSubmodule
          (fun z ↦ generator F ν ω W r (z + d)),
        ∀ f : GlobalBruhat F, ∀ z : ℂ, (e (U.rangeRestrict ((H F η ω).mkQ f))).val.val z =
          Z F ν ω (globalWeilPrincipalValues F W f) (z + d) := by
  intro U
  have hk : H F η ω = (globalHomogeneousThetaOperator F ν ω).ker :=
    globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν ω
  have hTop : X F η ω = ⊤ := by
    have h := globalPolarFree_image_eq_top_of_ne_one F ν ω hω
    rw [← hk] at h
    exact h
  let j : X F η ω ≃ₗ[ℂ] Q F η ω := (LinearEquiv.ofEq _ _ hTop).trans Submodule.topEquiv
  let J : X F η ω ≃L[ℂ] Q F η ω := ⟨j, continuous_subtype_val, continuous_id.subtype_mk _⟩
  obtain ⟨K₀, hK₀⟩ := embeddedRange_equiv U
    (globalHomogeneousPrincipalValues_isClosedEmbedding F ν η μ hν ω W).isEmbedding
  obtain ⟨S, hS, hu, r, C, hC, hr, hmin, hEuler⟩ :=
    exists_globalConverse_eulerReference F ν η hν μ ω
  obtain ⟨e, he⟩ := exists_globalPV_polarFree_shift_equiv_of_min F ν η μ hν ω r hr hmin W d
  refine ⟨S, hS, hu, r, C, hC, hEuler, K₀.symm.trans (J.symm.trans e), fun f z ↦ ?_⟩
  let x := J.symm ((H F η ω).mkQ f)
  have hx : x.val = (H F η ω).mkQ f := rfl
  have hK : K₀.symm (U.rangeRestrict ((H F η ω).mkQ f)) = (H F η ω).mkQ f := by
    rw [← hK₀, K₀.symm_apply_apply]
  change (e (J.symm (K₀.symm (U.rangeRestrict ((H F η ω).mkQ f))))).val.val z = _
  rw [hK]
  change (e x).val.val z = _
  obtain ⟨g, hg, heq⟩ := Submodule.mem_map.mp x.property
  let g₀ : A F := ⟨g, hg⟩
  have hX : x = globalPolarFreeTestClass F η ω g₀ := Subtype.ext heq.symm
  rw [hX, he]
  have hPV : (H F η ω).mkQ (globalWeilPrincipalValues F W g) =
      (H F η ω).mkQ (globalWeilPrincipalValues F W f) := by
    have hq := congrArg U (heq.trans hx)
    change V F ν η μ hν ω W ((H F η ω).mkQ g) =
      V F ν η μ hν ω W ((H F η ω).mkQ f) at hq
    simpa only [globalHomogeneousPrincipalValues_mk] using hq
  exact congrFun (globalMellin_eq_of_mkQ_eq F η ω ν hν hPV) (z + d)

include μ hν in
/-- On a nontrivial component the pole-free principal-value classes fill
the whole principal-value theta image, yielding the zero-cokernel sequence. -/
theorem globalPV_nontrivial_polar_image_eq_full (hω : ω ≠ 1) (W : Finset (Place F)) :
    (X F η ω).map (V F ν η μ hν ω W).toLinearMap = (V F ν η μ hν ω W).toLinearMap.range := by
  have hk : H F η ω = (globalHomogeneousThetaOperator F ν ω).ker :=
    globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν ω
  have h := globalPolarFree_image_eq_top_of_ne_one F ν ω hω
  rw [← hk] at h
  have ht : X F η ω = ⊤ := h
  rw [ht, Submodule.map_top]

include μ hν in
/-- The trivial principal-value converse uses a common normalized Hecke
reference for the pole-free test map and the full meromorphic middle term. -/
theorem exists_globalPV_trivial_shift_converse (W : Finset (Place F)) (d : ℂ) :
    let U := polarPrincipalTests F W
    let M := globalRegularPrincipalMellin F ν η μ hν 1 W d
    ∃ (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (1 : PontryaginDual (K F)) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (r : GlobalBruhat F) (C : ℂ), C ≠ 0 ∧
      EqOn (Z F ν 1 r) (fun z ↦ C * globalCompletedHeckeEuler F 1 S hs hu z) {z | 1 < z.re} ∧
      let D := bergmanDivisorSubmodule (fun z ↦ generator F ν 1 W r (z + d))
      IsClosed (D : Set B) ∧
      (∃ L : U.toLinearMap.range →L[ℂ] D,
        IsOpenQuotientMap L ∧
        L.toLinearMap.ker = ((H F η 1).comap (A F).subtype).map U.rangeRestrict.toLinearMap ∧
        ∀ f : U.toLinearMap.range, ∀ z : ℂ, (L f).val.val z = Z F ν 1 f.val (z + d)) ∧
      (∃ e : X F η 1 ≃L[ℂ] D, ∀ x : X F η 1, ∀ z : globalShiftedMellinRegularSet d,
        (e x).val.val z.val = M x.val z) ∧
      ∀ u : globalShiftedMellinRegularSet d → ℂ, u ∈ M.range ↔
        ∃ b : B, b ∈ D ∧ ∀ z : globalShiftedMellinRegularSet d,
          b.val z.val = (z.val + d) * (1 - z.val - d) * u z := by
  intro U M
  obtain ⟨S, hs, hu, r, C, hC, hr, hmin, hEuler⟩ :=
    exists_globalConverse_eulerReference F ν η hν μ 1
  have hd : Differentiable ℂ (fun z ↦ generator F ν 1 W r (z + d)) :=
    (generator_differentiable F ν 1 W r).comp (differentiable_id.add_const d)
  refine ⟨S, hs, hu, r, C, hC, hEuler, bergmanDivisorSubmodule_isClosed hd,
    exists_globalPV_test_shift_map_of_min F ν η μ hν 1 r hr hmin W d, ?_,
    globalRegularPrincipalMellin_trivial_range_of_min F ν η μ hν r hr hmin W d⟩
  obtain ⟨e, he⟩ := exists_globalPV_polarFree_shift_equiv_of_min F ν η μ hν 1 r hr hmin W d
  refine ⟨e, fun x z ↦ ?_⟩
  obtain ⟨f, hf, hx⟩ := Submodule.mem_map.mp x.property
  let f₀ : A F := ⟨f, hf⟩
  have h : x = globalPolarFreeTestClass F η 1 f₀ := Subtype.ext hx.symm
  rw [h, he]
  change _ = globalRegularPrincipalMellin F ν η μ hν 1 W d ((H F η 1).mkQ f) z
  rw [globalRegularPrincipalMellin_mk]

/-- The regular principal-value chart evaluates the actual continuation for
the input Hecke character, expressed as a norm twist of its compact part. -/
theorem globalRegularPrincipalMellin_normTwist_mk (W : Finset (Place F)) (d : ℂ)
    (f : GlobalBruhat F) (z : globalShiftedMellinRegularSet d) :
    globalRegularPrincipalMellin F ν η μ hν ω W d ((H F η ω).mkQ f) z =
      globalZetaContinued F ν (globalWeilPrincipalValues F W f)
        (ideleNormTwist F (compactIdeleClassCharacter F ω) d) d z.val := by
  rw [globalRegularPrincipalMellin_mk, globalZetaContinued_compact_twist]

#print axioms exists_globalPV_polarFree_shift_equiv_of_min
#print axioms globalRegularPrincipalMellin_trivial_range_of_min
#print axioms globalTrivialPrincipalMellin_residue_exact
#print axioms exists_globalPV_test_shift_map_of_min
#print axioms exists_globalPV_nontrivial_shift_converse
#print axioms globalPV_nontrivial_polar_image_eq_full
#print axioms exists_globalPV_trivial_shift_converse
#print axioms globalRegularPrincipalMellin_normTwist_mk

end

end Masullo
