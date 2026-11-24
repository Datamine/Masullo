import SLocalLaurentFormula

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Local (v : S) := locallyConstantTests (v.val.adicCompletion F)
private abbrev Finite := locallyConstantTests ((v : S) → v.val.adicCompletion F)

private def pureTest (φ : Arch F) (g : ∀ w : S, Local F S w) : E F S :=
  sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)

private theorem pureTest_span :
    Submodule.span ℂ (range (fun a : Arch F × (∀ w : S, Local F S w) ↦ pureTest F S a.1 a.2)) = ⊤ := by
  let D := Submodule.span ℂ (range (fun a : Arch F × (∀ w : S, Local F S w) ↦ pureTest F S a.1 a.2))
  have hPure (φ : Arch F) (ψ : Finite F S) : sLocalBruhatPure F S φ ψ ∈ D := by
    have hψ : ψ ∈ Submodule.span ℂ (range (locallyConstantTestPiProduct
        (X := fun v : S => v.val.adicCompletion F))) := by
      rw [locallyConstantTest_span_piProduct]
      trivial
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨(φ,g), rfl⟩
    | zero => rw [map_zero]; exact D.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact D.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact D.smul_mem c hx
  apply top_unique
  rw [← sLocalBruhatPure_span F S]
  apply Submodule.span_le.mpr
  rintro _ ⟨φ, ψ, rfl⟩
  exact hPure φ ψ

private def principalFactors (T : Finset S) (g : ∀ v : S, Local F S v) (v : S) : Local F S v :=
  if v ∈ T then weilPrincipalValue F v.val (g v) else g v

private theorem sLocalPrincipalValues_pureTest (T : Finset S) (φ : Arch F) (g : ∀ v : S, Local F S v) :
    sLocalWeilPrincipalValues F S T (pureTest F S φ g) = pureTest F S φ (principalFactors F S T g) := by
  induction T using Finset.induction_on with
  | empty =>
    have he : principalFactors F S ∅ g = g := by funext v; simp [principalFactors]
    rw [he]
    rfl
  | insert v T hT hIH =>
    have hp : sLocalWeilPrincipalValues F S (insert v T) =
        sLocalWeilPrincipalValue F S v * sLocalWeilPrincipalValues F S T :=
      Finset.noncommProd_insert_of_notMem T v _ _ hT
    rw [hp]
    change sLocalWeilPrincipalValue F S v (sLocalWeilPrincipalValues F S T (pureTest F S φ g)) = _
    rw [hIH]
    change sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v (weilPrincipalValue F v.val))
        (sLocalBruhatPure F S φ (locallyConstantTestPiProduct (principalFactors F S T g))) = _
    rw [sLocalBruhatFiniteMap_pure, sLocalCoordinateMap_piProduct]
    have he : Function.update (principalFactors F S T g) v
        (weilPrincipalValue F v.val (principalFactors F S T g v)) =
        principalFactors F S (insert v T) g := by
      funext w
      by_cases h : w = v
      · subst w
        simp [principalFactors, hT]
      · simp [principalFactors, h]
    rw [he]
    rfl

/-- The tensor subspace with every selected finite local factor vanishing
at zero. Local constancy makes this the zero extension of tests supported
in the corresponding multiplicative local fields. -/
def sLocalFiniteNonzeroTestSubspace (T : Finset S) : Submodule ℂ (E F S) :=
  Submodule.span ℂ {f | ∃ (φ : Arch F) (g : ∀ v : S, Local F S v),
    (∀ v ∈ T, (g v).val 0 = 0) ∧ pureTest F S φ g = f}

/-- Finite principal values have exactly the indicated zero-extension
tensor range on the actual Schwartz–Bruhat tests. -/
theorem sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace (T : Finset S) :
    (sLocalWeilPrincipalValues F S T).range = sLocalFiniteNonzeroTestSubspace F S T := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    have hf : f ∈ Submodule.span ℂ (range (fun a : Arch F × (∀ w : S, Local F S w) ↦
        pureTest F S a.1 a.2)) := by rw [pureTest_span F S]; trivial
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨φ,g⟩, rfl⟩ := hx
      change sLocalWeilPrincipalValues F S T (pureTest F S φ g) ∈ _
      rw [sLocalPrincipalValues_pureTest]
      refine Submodule.subset_span ⟨φ, principalFactors F S T g, ?_, rfl⟩
      intro v hv
      rw [principalFactors, ite_eq_left hv]
      exact (Set.ext_iff.mp (weilPrincipalValue_range F v.val) _).mp
        (mem_range_self (g v))
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨φ, g, hg, rfl⟩
    have hex (v : S) : ∃ a : Local F S v,
        (if v ∈ T then weilPrincipalValue F v.val a else a) = g v := by
      by_cases h : v ∈ T
      · have hr : g v ∈ range (weilPrincipalValue F v.val) :=
          (Set.ext_iff.mp (weilPrincipalValue_range F v.val) _).mpr (hg v h)
        obtain ⟨a, ha⟩ := hr
        exact ⟨a, by rwa [ite_eq_left h]⟩
      · exact ⟨g v, by rw [ite_eq_right h]⟩
    choose g' hg' using hex
    have he : principalFactors F S T g' = g := funext hg'
    refine ⟨pureTest F S φ g', ?_⟩
    change sLocalWeilPrincipalValues F S T (pureTest F S φ g') = pureTest F S φ g
    rw [sLocalPrincipalValues_pureTest, he]

theorem sLocalFiniteNonzeroTestSubspace_isClosed (T : Finset S) :
    IsClosed (sLocalFiniteNonzeroTestSubspace F S T : Set (E F S)) := by
  rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
  exact (sLocalWeilPrincipalValues_closedEmbedding F S T).isClosed_range

private def unitsZeroExtendFun {L : Type*} [Field L] [TopologicalSpace L]
    (g : locallyConstantTests Lˣ) (x : L) : ℂ :=
  if h : x ≠ 0 then g.val (Units.mk0 x h) else 0

@[simp] private theorem unitsZeroExtendFun_units {L : Type*} [Field L] [TopologicalSpace L]
    (g : locallyConstantTests Lˣ) (u : Lˣ) :
    unitsZeroExtendFun g u.val = g.val u := by
  rw [unitsZeroExtendFun, dite_eq_left u.ne_zero]
  exact congrArg g.val (Units.ext rfl)

/-- Zero extension of compactly supported locally constant multiplicative tests. -/
def finiteLocalUnitZeroExtend (v : S) (g : locallyConstantTests (v.val.adicCompletion F)ˣ) : Local F S v := by
  let L := v.val.adicCompletion F
  let j : Lˣ → L := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  let C : Set L := j '' tsupport g.val
  have hC : IsCompact C := g.property.2.image hj.continuous
  have hzero (x : L) (hx : x ∉ C) : unitsZeroExtendFun g x = 0 := by
    by_cases h : x = 0
    · simp [unitsZeroExtendFun, h]
    · let u := Units.mk0 x h
      have hux : j u = x := rfl
      have hu : u ∉ tsupport g.val := fun hu ↦ hx ⟨u, hu, hux⟩
      exact (unitsZeroExtendFun_units g u).trans (image_eq_zero_of_notMem_tsupport hu)
  refine ⟨unitsZeroExtendFun g, ?_, HasCompactSupport.intro hC hzero⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases h : x = 0
  · subst x
    have h0 : (0 : L) ∉ C := by rintro ⟨u, -, hu⟩; exact u.ne_zero hu
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds h0] with y hy
    exact (hzero y hy).trans (hzero 0 h0).symm
  · let u := Units.mk0 x h
    have hux : j u = x := rfl
    rw [← hux, ← hj.map_nhds_eq u]
    change ∀ᶠ t in 𝓝 u, unitsZeroExtendFun g t.val = unitsZeroExtendFun g u.val
    simp only [unitsZeroExtendFun_units]
    have hg := g.property.1
    rw [IsLocallyConstant.iff_eventually_eq] at hg
    exact hg u

/-- The local zero-extension image consists exactly of additive tests
vanishing at zero. -/
theorem finiteLocalUnitZeroExtend_range (v : S) :
    range (finiteLocalUnitZeroExtend F S v) = {f : Local F S v | f.val 0 = 0} := by
  let L := v.val.adicCompletion F
  let j : Lˣ → L := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    simp [finiteLocalUnitZeroExtend, unitsZeroExtendFun]
  · intro h0
    have hcl : IsClosed (Function.support f.val) := by
      have he : Function.support f.val = {x | f.val x = 0}ᶜ := rfl
      rw [he]
      exact (f.property.1.isOpen_fiber 0).isClosed_compl
    have hcf : IsCompact (Function.support f.val) := by
      have he := hcl.closure_eq
      exact he ▸ f.property.2
    let g : locallyConstantTests Lˣ := ⟨f.val ∘ j, f.property.1.comp_continuous hj.continuous, by
      have hc : IsCompact (Function.support (f.val ∘ j)) := by
        apply hj.isEmbedding.isCompact_iff.mpr
        have he : j '' Function.support (f.val ∘ j) = Function.support f.val := by
          ext x
          constructor
          · rintro ⟨u, hu, rfl⟩
            exact hu
          · intro hx
            have hn : x ≠ 0 := fun he ↦ hx (he ▸ h0)
            exact ⟨Units.mk0 x hn, hx, rfl⟩
        rw [he]
        exact hcf
      have hclosed : IsClosed (Function.support (f.val ∘ j)) := by
        change IsClosed (j ⁻¹' Function.support f.val)
        exact hcl.preimage hj.continuous
      change IsCompact (closure (Function.support (f.val ∘ j)))
      rwa [hclosed.closure_eq]⟩
    refine ⟨g, Subtype.ext (funext fun x ↦ ?_)⟩
    change unitsZeroExtendFun g x = f.val x
    by_cases hx : x = 0
    · subst x
      simpa [unitsZeroExtendFun] using h0.symm
    · rw [unitsZeroExtendFun, dite_eq_left hx]
      rfl

/-- A locally constant additive test vanishing at the origin has compact
support after restriction to the multiplicative local field. -/
theorem finiteTest_restrictUnits_hasCompactSupport (v : S) (f : Local F S v)
    (hf : f.val 0 = 0) : HasCompactSupport (fun u : (v.val.adicCompletion F)ˣ ↦ f.val u.val) := by
  have he : f ∈ range (finiteLocalUnitZeroExtend F S v) := by
    rw [finiteLocalUnitZeroExtend_range]
    exact hf
  obtain ⟨g, rfl⟩ := he
  change HasCompactSupport (fun u : (v.val.adicCompletion F)ˣ ↦ unitsZeroExtendFun g u.val)
  simpa only [unitsZeroExtendFun_units] using g.property.2
/-- The tensor subspaces in the principal-value range can be written using
actual compactly supported locally constant tests on the multiplicative fields. -/
theorem sLocalFiniteNonzeroTestSubspace_eq_zeroExtensions (T : Finset S) :
    sLocalFiniteNonzeroTestSubspace F S T = Submodule.span ℂ
      {f | ∃ (φ : Arch F) (g : ∀ v : S, Local F S v),
        (∀ v ∈ T, ∃ t : locallyConstantTests (v.val.adicCompletion F)ˣ,
          finiteLocalUnitZeroExtend F S v t = g v) ∧ pureTest F S φ g = f} := by
  unfold sLocalFiniteNonzeroTestSubspace
  congr 1
  ext f
  apply exists_congr
  intro φ
  apply exists_congr
  intro g
  apply and_congr_left
  intro _
  apply forall_congr'
  intro v
  apply imp_congr_right
  intro _
  exact (Set.ext_iff.mp (finiteLocalUnitZeroExtend_range F S v) (g v)).symm

/-- The finite places where the fixed norm-one character is unramified. -/
def sLocalUnramifiedPlaceSelection (ω : PontryaginDual (K F S)) : Finset S :=
  Finset.univ.filter fun v ↦ finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)

private theorem multiplier_unramifiedSelection (ω : PontryaginDual (K F S)) (z : ℂ) :
    sLocalSelectedEulerMultiplier F S ω (sLocalUnramifiedPlaceSelection F S ω) z =
      sLocalSelectedEulerMultiplier F S ω Finset.univ z := by
  unfold sLocalSelectedEulerMultiplier sLocalUnramifiedPlaceSelection
  apply Finset.prod_filter_of_ne
  intro v _ hv
  by_contra h
  exact hv (ite_eq_right h)

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (ν : Measure (K F S)) [ν.IsHaarMeasure]

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ)
  Measure.count (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

private abbrev M (ω : PontryaginDual (K F S)) := sLocalHomogeneousThetaKernel F S ν ω

include hν in
set_option maxHeartbeats 1800000 in
/-- Applying the full finite product or just the unramified factors gives
the same class on the chosen homogeneous theta quotient. -/
theorem sLocalWeilPrincipalValues_unramified_mk (ω : PontryaginDual (K F S)) (f : E F S) :
    (M F S ν ω).mkQ (sLocalWeilPrincipalValues F S (sLocalUnramifiedPlaceSelection F S ω) f) =
      (M F S ν ω).mkQ (sLocalWeilPrincipalValues F S Finset.univ f) := by
  let A := sLocalWeilPrincipalValues F S (sLocalUnramifiedPlaceSelection F S ω) f
  let B := sLocalWeilPrincipalValues F S Finset.univ f
  apply sLocalHomogeneousContinuedMellin_injective F S μ ν hν ω
  apply ContinuousMap.ext
  intro z
  change Z F S μ ω A z.val = Z F S μ ω B z.val
  have hA := sLocalWeilPrincipalValues_continued F S μ ν hν ω
    (sLocalUnramifiedPlaceSelection F S ω) f z.val
  have hB := sLocalWeilPrincipalValues_continued F S μ ν hν ω Finset.univ f z.val
  have he : Z F S μ ω A =ᶠ[𝓝[≠] z.val] Z F S μ ω B := by
    filter_upwards [hA, hB] with w ha hb
    exact ha.trans ((congrArg (· * Z F S μ ω f w)
      (multiplier_unramifiedSelection F S ω w)).trans hb.symm)
  have hc (g : E F S) : ContinuousAt (Z F S μ ω g) z.val :=
    (sLocalProductZetaContinued_continuousOn_regular F S μ ω g z.val z.property).continuousAt
      ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds z.property)
  exact (((hc A).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hc B)).mp he).eq_of_nhds

include hν in
set_option maxHeartbeats 1800000 in
/-- The two closed finite-support conditions in (5.3.4.15) give the
same homogeneous theta image, namely the image of the full Weil product. -/
theorem sLocalFiniteNonzeroTestSubspace_images (ω : PontryaginDual (K F S)) :
    let q := (M F S ν ω).mkQ
    (sLocalFiniteNonzeroTestSubspace F S (sLocalUnramifiedPlaceSelection F S ω)).map q =
      (sLocalFiniteNonzeroTestSubspace F S Finset.univ).map q ∧
    ((sLocalFiniteNonzeroTestSubspace F S Finset.univ).map q : Set _) =
      range (fun f ↦ q (sLocalWeilPrincipalValues F S Finset.univ f)) := by
  intro q
  rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace,
    ← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
  constructor
  · apply Submodule.ext
    intro x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, (sLocalWeilPrincipalValues_unramified_mk F S μ ν hν ω g).symm⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, sLocalWeilPrincipalValues_unramified_mk F S μ ν hν ω g⟩
  · ext x
    exact ⟨fun ⟨_, ⟨f, rfl⟩, hx⟩ ↦ ⟨f, hx⟩, fun ⟨f, hx⟩ ↦ ⟨_, ⟨f, rfl⟩, hx⟩⟩

include hν in
/-- The full Weil product leaves only the archimedean pole bound,
including multiplicities of coinciding local Gamma factors. -/
theorem sLocalWeilPrincipalValues_archPoleBound (ω : PontryaginDual (K F S)) (f : E F S) (c : ℂ) :
    ((-(sLocalArchPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (Z F S μ ω (sLocalWeilPrincipalValues F S Finset.univ f)) c := by
  have he : sLocalSelectedFinitePoleCount F S ω Finset.univ c = (sLocalFinitePolesAt F S ω c).card := rfl
  have hb := sLocalWeilPrincipalValues_pole_le F S μ ν hν ω Finset.univ f c
  rw [he, sLocalPoleCount] at hb
  have h : ((sLocalFinitePolesAt F S ω c).card : ℤ) -
      ((sLocalArchPoleCount F S ω c + (sLocalFinitePolesAt F S ω c).card : ℕ) : ℤ) =
        -(sLocalArchPoleCount F S ω c : ℤ) := by omega
  rwa [h] at hb

include hν in
/-- An actual pole after the full finite principal-value product lies on
one of the real or complex Gamma pole lattices. -/
theorem sLocalWeilPrincipalValues_archPoleLocation (ω : PontryaginDual (K F S)) (f : E F S) (c : ℂ)
    (hc : meromorphicOrderAt (Z F S μ ω (sLocalWeilPrincipalValues F S Finset.univ f)) c < 0) :
    (∃ (v : {w : InfinitePlace F // w.IsReal}) (n : ℕ),
      c = -(sLocalRealArchParameters F S ω v).1 -
        ((sLocalRealArchParameters F S ω v).2 % 2 : ℕ) - 2 * (n : ℂ)) ∨
    (∃ (v : {w : InfinitePlace F // w.IsComplex}) (n : ℕ),
      c = -(sLocalComplexArchParameters F S ω v).1 -
        ((sLocalComplexArchParameters F S ω v).2.natAbs : ℂ) / 2 - (n : ℂ)) := by
  have hcount : 0 < sLocalArchPoleCount F S ω c := by
    by_contra h
    have hz : sLocalArchPoleCount F S ω c = 0 := by omega
    have hb := sLocalWeilPrincipalValues_archPoleBound F S μ ν hν ω f c
    simp only [hz, Nat.cast_zero, neg_zero, WithTop.coe_zero] at hb
    exact (not_lt_of_ge hb) hc
  let R := Finset.univ.filter (fun v : {w : InfinitePlace F // w.IsReal} ↦
    realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
      (c + (sLocalRealArchParameters F S ω v).1) = 0)
  let C := Finset.univ.filter (fun v : {w : InfinitePlace F // w.IsComplex} ↦
    complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
      (c + (sLocalComplexArchParameters F S ω v).1) = 0)
  change 0 < R.card + C.card at hcount
  have h : 0 < R.card ∨ 0 < C.card := by omega
  rcases h with hR | hC
  · obtain ⟨v, hv⟩ := Finset.card_pos.mp hR
    have hv₀ := (Finset.mem_filter.mp hv).2
    obtain ⟨n, hn⟩ := (realArchZetaDenominator_eq_zero_iff _ _).mp hv₀
    exact Or.inl ⟨v, n, by linear_combination hn⟩
  · obtain ⟨v, hv⟩ := Finset.card_pos.mp hC
    have hv₀ := (Finset.mem_filter.mp hv).2
    obtain ⟨n, hn⟩ := (complexArchZetaDenominator_eq_zero_iff _ _).mp hv₀
    exact Or.inr ⟨v, n, by linear_combination hn⟩

/-- The homogeneous image of the full finite principal-value product. -/
def sLocalArchPolarImage (ω : PontryaginDual (K F S)) :
    Submodule ℂ (SLocalHomogeneousThetaQuotient F S ν ω) :=
  (sLocalFiniteNonzeroTestSubspace F S Finset.univ).map (M F S ν ω).mkQ

/-- The entire-Mellin subspace within the full finite principal-value image. -/
def sLocalArchPolarKernel (ω : PontryaginDual (K F S)) :
    Submodule ℂ (sLocalArchPolarImage F S ν ω) :=
  (sLocalThetaPoleBound F S μ ν hν ω (fun _ ↦ 0)).comap
    (sLocalArchPolarImage F S ν ω).subtype

/-- The archimedean principal-part quotient is nuclear with its quotient
topology. This uses the induced topology on the actual principal-value image. -/
theorem sLocalArchPolarQuotient_nuclear (ω : PontryaginDual (K F S)) :
    NuclearLocallyConvex.{u, u}
      (sLocalArchPolarImage F S ν ω ⧸ sLocalArchPolarKernel F S μ ν hν ω) := by
  have hQ := (sLocalHomogeneousTheta_primalStructure F S ν ω).1
  have hI := nuclearLocallyConvex_submodule hQ (sLocalArchPolarImage F S ν ω)
  have hK : IsClosed (sLocalArchPolarKernel F S μ ν hν ω : Set (sLocalArchPolarImage F S ν ω)) :=
    (sLocalThetaPoleBound_isClosed F S μ ν hν ω (fun _ ↦ 0)).preimage continuous_subtype_val
  exact nuclearLocallyConvex_quotient hI _ hK

end

end Masullo
