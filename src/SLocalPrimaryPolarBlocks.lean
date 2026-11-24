import SLocalPrimaryJetInterpolation
import SLocalOrbitalInterpolation

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

theorem biorthogonal_block_sum_apply
    {X B : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    {I : B → Type*} [∀ c, Fintype (I c)]
    (x : (Σ c, I c) → X) (D : (Σ c, I c) → StrongDual ℂ X)
    (h : ∀ i j, D i (x j) = if i = j then 1 else 0) (c : B)
    (i : Σ c, I c) (y : X) :
    D i (∑ j : I c, D ⟨c,j⟩ y • x ⟨c,j⟩) = if i.1 = c then D i y else 0 := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, h]
  split_ifs with hc
  · rcases i with ⟨b,k⟩
    change b = c at hc
    subst b
    simp
  · apply Finset.sum_eq_zero
    intro j _
    have hne : i ≠ ⟨c,j⟩ := fun he ↦ hc (congrArg Sigma.fst he)
    simp [hne]

/-- Two biorthogonal coordinate systems give the same finite block projections
when the new coordinates at each center detect the same local zero data. -/
private theorem finite_block_transfer
    {X B : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    {I K : B → Type*} [∀ c, Fintype (I c)] [∀ c, Fintype (K c)]
    (x : (Σ c, I c) → X) (D : (Σ c, I c) → StrongDual ℂ X)
    (u : (Σ c, K c) → X) (L : (Σ c, K c) → StrongDual ℂ X)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hL : ∀ i j, L i (u j) = if i = j then 1 else 0)
    (hsep : ∀ y : X, (∀ i, D i y = 0) → y = 0)
    (hlocal : ∀ (c : B) (y : X), (∀ k : K c, L ⟨c,k⟩ y = 0) →
      ∀ i : I c, D ⟨c,i⟩ y = 0)
    (hprimal : ∀ y : X, HasSum (fun i ↦ D i y • x i) y)
    (habsolute : ∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
      ∀ y : X, Summable (fun i ↦ q (D i y • x i)) ∧ (∑' i, q (D i y • x i)) ≤ r y)
    (hdual : ∀ g : StrongDual ℂ X, HasSum (fun i ↦ g (x i) • D i) g) :
    let P (c : B) (y : X) := ∑ k : K c, L ⟨c,k⟩ y • u ⟨c,k⟩
    (∀ y : X, HasSum (fun c ↦ P c y) y) ∧
    (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
      ∀ y : X, Summable (fun c ↦ q (P c y)) ∧ (∑' c, q (P c y)) ≤ r y) ∧
    ∀ g : StrongDual ℂ X, HasSum (fun c ↦ ∑ k : K c, g (u ⟨c,k⟩) • L ⟨c,k⟩) g := by
  let P (c : B) (y : X) := ∑ k : K c, L ⟨c,k⟩ y • u ⟨c,k⟩
  let Q (c : B) (y : X) := ∑ i : I c, D ⟨c,i⟩ y • x ⟨c,i⟩
  have hP (c : B) (y : X) : P c y = Q c y := by
    apply sub_eq_zero.mp
    apply hsep
    rintro ⟨b,i⟩
    have hQ := biorthogonal_block_sum_apply x D hD c ⟨b,i⟩ y
    by_cases hbc : b = c
    · subst b
      have hn (k : K c) : L ⟨c,k⟩ (P c y - y) = 0 := by
        rw [map_sub, show L ⟨c,k⟩ (P c y) = L ⟨c,k⟩ y by
          simpa [P] using biorthogonal_block_sum_apply u L hL c ⟨c,k⟩ y, sub_self]
      have hd := hlocal c (P c y - y) hn i
      rw [map_sub, sub_eq_zero] at hd
      have he : D ⟨c,i⟩ (Q c y) = D ⟨c,i⟩ y := by simpa [Q] using hQ
      rw [map_sub, hd, he, sub_self]
    · have hn (k : K b) : L ⟨b,k⟩ (P c y) = 0 := by
        simpa [P, hbc] using biorthogonal_block_sum_apply u L hL c ⟨b,k⟩ y
      have he : D ⟨b,i⟩ (Q c y) = 0 := by simpa [Q, hbc] using hQ
      rw [map_sub, hlocal b (P c y) hn i, he, sub_self]
  have hinj : Injective (fun y : X ↦ fun i ↦ D i y) := by
    intro y z h
    exact sub_eq_zero.mp (hsep _ fun i ↦ by rw [map_sub, sub_eq_zero]; exact congrFun h i)
  letI : T2Space X := T2Space.of_injective_continuous hinj (continuous_pi fun i ↦ (D i).continuous)
  refine ⟨fun y ↦ ?_, fun q hq ↦ ?_, fun g ↦ ?_⟩
  · have hs : HasSum (fun c ↦ Q c y) y :=
      (hprimal y).sigma fun c ↦ hasSum_fintype _
    simpa only [← hP] using hs
  · obtain ⟨r, hr, hb⟩ := habsolute q hq
    refine ⟨r, hr, fun y ↦ ?_⟩
    obtain ⟨hs, hsy⟩ := hb y
    have hfib : HasSum (fun c ↦ ∑ i : I c, q (D ⟨c,i⟩ y • x ⟨c,i⟩))
        (∑' i, q (D i y • x i)) := hs.hasSum.sigma fun c ↦ hasSum_fintype _
    have hle (c : B) : q (P c y) ≤ ∑ i : I c, q (D ⟨c,i⟩ y • x ⟨c,i⟩) := by
      rw [hP]
      exact Finset.le_sum_of_subadditive q (map_zero _).le (map_add_le_add q) _ _
    have hsum := hfib.summable.of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) hle
    exact ⟨hsum, (hsum.tsum_le_tsum hle hfib.summable).trans (hfib.tsum_eq.le.trans hsy)⟩
  · have hs : HasSum (fun c ↦ ∑ i : I c, g (x ⟨c,i⟩) • D ⟨c,i⟩) g :=
      (hdual g).sigma fun c ↦ hasSum_fintype _
    apply hs.congr_fun
    intro c
    ext y
    have he := congrArg g (hP c y)
    simpa [P, Q, map_smul, mul_comm] using he

private theorem hasSum_of_subsingleton_blocks
    {B X : Type*} [AddCommMonoid X] [TopologicalSpace X]
    {I : B → Type*} [∀ c, Fintype (I c)] [∀ c, Subsingleton (I c)]
    (f : (Σ b, I b) → X) {a : X}
    (h : HasSum (fun b ↦ ∑ i : I b, f ⟨b,i⟩) a) : HasSum f a := by
  have hinj : Injective (Sigma.fst : (Σ b, I b) → B) := by
    rintro ⟨b,i⟩ ⟨c,j⟩ hbc
    change b = c at hbc
    subst c
    rw [Subsingleton.elim i j]
  have hz (b : B) (hb : b ∉ range (Sigma.fst : (Σ b, I b) → B)) :
      (∑ i : I b, f ⟨b,i⟩) = 0 := by
    letI : IsEmpty (I b) := ⟨fun i ↦ hb ⟨⟨b,i⟩,rfl⟩⟩
    simp
  refine ((hinj.hasSum_iff hz).mpr h).congr_fun ?_
  rintro ⟨b,i⟩
  exact (Fintype.sum_subsingleton (fun j : I b ↦ f ⟨b,j⟩) i).symm
variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
  (hνG : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
  (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hνS : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F))
    Measure.count (sLocalClassHaar F S ν))

variable (hS : ∀ v : HeightOneSpectrum (𝓞 F),
  v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S (fun v ↦ μ v.val) ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

set_option maxHeartbeats 700000 in
include hνG hνS in
/-- The polar coordinates give an absolute expansion by complete pole blocks
of the primary quotient and an unconditional block expansion of its strong dual. -/
theorem exists_sLocalPrimaryQuotient_polar_blocks_all_stages
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let d := sLocalPoleCount F S A
    let t := sLocalSelectedFinitePoleCount F S A W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let B (c : ℂ) := ↥(Finset.Ioc (d c - t c) (d c))
    ∃ (u : (Σ c : ℂ, B c) → X) (L : (Σ c : ℂ, B c) → StrongDual ℂ X),
      (∀ i f, L i (R.mkQ (M.mkQ f)) = sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f) ∧
      (∀ i j, L i (u j) = if i = j then 1 else 0) ∧
      let P (c : ℂ) (y : X) := ∑ k : B c, L ⟨c,k⟩ y • u ⟨c,k⟩
      (∀ y : X, HasSum (fun c ↦ P c y) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun c ↦ q (P c y)) ∧ (∑' c, q (P c y)) ≤ r y) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun c ↦ ∑ k : B c, g (u ⟨c,k⟩) • L ⟨c,k⟩) g := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let d := sLocalPoleCount F S A
  let t := sLocalSelectedFinitePoleCount F S A W
  let M := sLocalHomogeneousThetaKernel F S ν A
  let Y := SLocalHomogeneousThetaQuotient F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := Y ⧸ R
  let B (c : ℂ) := ↥(Finset.Ioc (d c - t c) (d c))
  let C (c : ℂ) := Fin (t c)
  let J := SLocalPrimaryEulerJetIndex F S A p W
  let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
  let V (i : Σ c, B c) := sLocalThetaLaurentCoeff F S (fun v ↦ μ v.val) ν hνS A i.1 i.2.val
  let a (i : Σ c, B c) : SLocalOrbitalIndex F S A W :=
    ⟨(i.1, i.2.val), Finset.mem_Ioc.mp i.2.property⟩
  have ha : Injective a := by
    rintro ⟨c,k⟩ ⟨c',k'⟩ h
    have he := congrArg Subtype.val h
    have hc : c = c' := congrArg Prod.fst he
    subst c'
    exact congrArg (Sigma.mk c) (Subtype.ext (congrArg Prod.snd he))
  obtain ⟨_, hR, _, u₀, hu₀, _⟩ :=
    sLocalOrbitalPrincipalValues_biorthogonal F S (fun v ↦ μ v.val) ν hνS A W
  let u (i : Σ c, B c) := u₀ (a i)
  let L (i : Σ c, B c) : StrongDual ℂ X :=
    R.liftQL (V i) (fun y hy ↦ (hR y).mp hy (a i))
  have hL (i j : Σ c, B c) : L i (u j) = if i = j then 1 else 0 := by
    obtain ⟨y, hy⟩ := R.mkQ_surjective (u j)
    rw [← hy]
    change V i y = _
    have hb := hu₀ (a i) (a j) y hy
    simpa only [ha.eq_iff] using hb
  have hLval (i : Σ c, B c) (f : E F S) :
      L i (Q f) = sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f := rfl
  have hQ : Surjective Q := R.mkQ_surjective.comp M.mkQ_surjective
  obtain ⟨x₀, D₀, hval, hD₀, hprimal, habs, _, hdual⟩ :=
    exists_sLocalPrimaryQuotient_compressedFourier_bases F S (μG := μ) (η := η)
      (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  let e : J × ℤ ≃ (Σ c, C c) := sLocalPrimaryEulerJetEquiv F S A hp hW
  let x (i : Σ c, C c) := x₀ (e.symm i)
  let D (i : Σ c, C c) := D₀ (e.symm i)
  have hDval (i : Σ c, C c) (f : E F S) :
      D i (Q f) = iteratedDeriv i.2.val
        (fun z : ℂ ↦ Z F S μ A⁻¹ (sLocalFourierCompression F S f) (1-z)) i.1 := by
    have he := sLocalPrimaryEulerJetEquiv_apply_values F S A hp hW (e.symm i)
    change (e (e.symm i)).1 = _ ∧ (e (e.symm i)).2.val = _ at he
    rw [e.apply_symm_apply] at he
    exact (hval (e.symm i) f).trans (congrArg₂ (fun (n : ℕ) (z : ℂ) ↦
      iteratedDeriv n (fun w : ℂ ↦ Z F S μ A⁻¹ (sLocalFourierCompression F S f) (1-w)) z)
      he.2.symm he.1.symm)
  have hsep (y : X) (hy : ∀ i, D i y = 0) : y = 0 := by
    obtain ⟨f, rfl⟩ := hQ y
    change R.mkQ (M.mkQ f) = 0
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    apply (sLocalOrbitalCompressedJets_ker_eq_principalValue_range
      F S μ η νG hνG ω hs hu ν hνS W f).mpr
    intro c k hk
    let i : Σ c, C c := ⟨c,⟨k,hk⟩⟩
    exact (hDval i f).symm.trans (hy i)
  have hlocal (c : ℂ) (y : X) (hy : ∀ k : B c, L ⟨c,k⟩ y = 0) (k : C c) :
      D ⟨c,k⟩ y = 0 := by
    obtain ⟨f, rfl⟩ := hQ y
    have hpole : 0 < t c := Nat.zero_le k.val |>.trans_lt k.isLt
    obtain ⟨a, _, n, hc, _⟩ := sLocalPrimaryEulerCell_represents F S A hp hW hpole
    have hre : c.re = 0 := by rw [hc]; simp [Complex.mul_re]
    have hband : ∀ j > d c - t c, sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c j f = 0 := by
      intro j hj
      by_cases htop : j ≤ d c
      · let i : B c := ⟨j,Finset.mem_Ioc.mpr ⟨hj,htop⟩⟩
        exact (hLval ⟨c,i⟩ f).symm.trans (hy i)
      · have hbound := sLocalZeta_poleOrder_le_euler F S (fun v ↦ μ v.val) A f c
        rw [sLocalEulerFactor_order F S A c, sLocalAllowedPoleOrder_eq_count F S A c] at hbound
        exact (sLocalLaurentCoeff_vanish_iff F S (fun v ↦ μ v.val) A c (d c) f).mpr
          hbound j (lt_of_not_ge htop)
    have hn := (sLocal_removedLaurent_iff_normalized_order F S (fun v ↦ μ v.val) A W f c).mp hband
    rw [hDval]
    exact (sLocalOrbitalCompressedJet_vanish_iff_normalized_order
      F S μ η νG hνG ω hs hu ν hνS f c hre (t c)).mpr hn k.val k.isLt
  refine ⟨u, L, hLval, hL, finite_block_transfer x D u L ?_ ?_ hsep hlocal ?_ ?_ ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa [D, x] using hD₀ (e.symm i) (e.symm i)
    · have hne := e.symm.injective.ne hij
      simpa [D, x, hij, hne] using hD₀ (e.symm i) (e.symm j)
  · intro i j
    by_cases hij : i = j <;> simpa [hij] using hL i j
  · intro y
    exact e.symm.hasSum_iff.mpr (hprimal y)
  · intro q hq
    obtain ⟨r, hr, hq'⟩ := habs q hq
    refine ⟨r, hr, fun y ↦ ?_⟩
    obtain ⟨hs, ht⟩ := hq' y
    exact ⟨e.symm.summable_iff.mpr hs, (e.symm.tsum_eq _).le.trans ht⟩
  · intro g
    exact e.symm.hasSum_iff.mpr (hdual g)

set_option maxHeartbeats 500000 in
include hνG hνS in
/-- If each selected center is simple, the polar expansions converge with
individual Laurent coefficients in any order. -/
theorem exists_sLocalPrimaryQuotient_polar_bases_of_simple_all_stages
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (hsimple : ∀ c : ℂ, sLocalSelectedFinitePoleCount F S
      (sLocalNormOneCharacterOfGlobal F ω S hs hu) W c ≤ 1) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let d := sLocalPoleCount F S A
    let t := sLocalSelectedFinitePoleCount F S A W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let I := Σ c : ℂ, ↥(Finset.Ioc (d c - t c) (d c))
    ∃ (u : I → X) (L : I → StrongDual ℂ X),
      (∀ i f, L i (R.mkQ (M.mkQ f)) = sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f) ∧
      (∀ i j, L i (u j) = if i = j then 1 else 0) ∧
      (∀ y : X, HasSum (fun i ↦ L i y • u i) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun i ↦ q (L i y • u i)) ∧ (∑' i, q (L i y • u i)) ≤ r y) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun i ↦ g (u i) • L i) g := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let d := sLocalPoleCount F S A
  let t := sLocalSelectedFinitePoleCount F S A W
  let B (c : ℂ) := ↥(Finset.Ioc (d c - t c) (d c))
  letI (c : ℂ) : Subsingleton (B c) := by
    apply Fintype.card_le_one_iff_subsingleton.mp
    have hd : t c ≤ d c := sLocalSelectedFinitePoleCount_le F S A W c
    have hs := hsimple c
    change t c ≤ 1 at hs
    simpa only [B, Fintype.card_coe, Nat.card_Ioc, Nat.sub_sub_self hd] using hs
  obtain ⟨u, L, hL, horth, hsum, habs, hdual⟩ :=
    exists_sLocalPrimaryQuotient_polar_blocks_all_stages F S (μ := μ) (η := η) (νG := νG)
      (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  refine ⟨u, L, hL, horth, fun y ↦ hasSum_of_subsingleton_blocks _ (hsum y), ?_,
    fun g ↦ hasSum_of_subsingleton_blocks _ (hdual g)⟩
  intro q hq
  obtain ⟨r, hr, h⟩ := habs q hq
  refine ⟨r, hr, fun y ↦ ?_⟩
  obtain ⟨hsy, hbound⟩ := h y
  let f (i : Σ c, B c) := q (L i y • u i)
  have he (c : ℂ) : (∑ k : B c, f ⟨c,k⟩) = q (∑ k : B c, L ⟨c,k⟩ y • u ⟨c,k⟩) := by
    rcases isEmpty_or_nonempty (B c) with h | h
    · letI : IsEmpty (B c) := h
      simp
    · obtain ⟨k⟩ := h
      simp only [Fintype.sum_subsingleton _ k, f]
  have hsum := hasSum_of_subsingleton_blocks f (hsy.hasSum.congr_fun he)
  exact ⟨hsum.summable, hsum.tsum_eq.le.trans hbound⟩


include hνG hνS hS in
theorem exists_sLocalPrimaryQuotient_polar_blocks
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let d := sLocalPoleCount F S A
    let t := sLocalSelectedFinitePoleCount F S A W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let B (c : ℂ) := ↥(Finset.Ioc (d c - t c) (d c))
    ∃ (u : (Σ c : ℂ, B c) → X) (L : (Σ c : ℂ, B c) → StrongDual ℂ X),
      (∀ i f, L i (R.mkQ (M.mkQ f)) = sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f) ∧
      (∀ i j, L i (u j) = if i = j then 1 else 0) ∧
      let P (c : ℂ) (y : X) := ∑ k : B c, L ⟨c,k⟩ y • u ⟨c,k⟩
      (∀ y : X, HasSum (fun c ↦ P c y) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun c ↦ q (P c y)) ∧ (∑' c, q (P c y)) ≤ r y) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun c ↦ ∑ k : B c, g (u ⟨c,k⟩) • L ⟨c,k⟩) g :=
  exists_sLocalPrimaryQuotient_polar_blocks_all_stages F S (μ := μ) (η := η) (νG := νG)
    (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW

include hνG hνS hS in
theorem exists_sLocalPrimaryQuotient_polar_bases_of_simple
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (hsimple : ∀ c : ℂ, sLocalSelectedFinitePoleCount F S
      (sLocalNormOneCharacterOfGlobal F ω S hs hu) W c ≤ 1) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let d := sLocalPoleCount F S A
    let t := sLocalSelectedFinitePoleCount F S A W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let I := Σ c : ℂ, ↥(Finset.Ioc (d c - t c) (d c))
    ∃ (u : I → X) (L : I → StrongDual ℂ X),
      (∀ i f, L i (R.mkQ (M.mkQ f)) = sLocalLaurentCoeff F S (fun v ↦ μ v.val) A i.1 i.2.val f) ∧
      (∀ i j, L i (u j) = if i = j then 1 else 0) ∧
      (∀ y : X, HasSum (fun i ↦ L i y • u i) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun i ↦ q (L i y • u i)) ∧ (∑' i, q (L i y • u i)) ≤ r y) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun i ↦ g (u i) • L i) g :=
  exists_sLocalPrimaryQuotient_polar_bases_of_simple_all_stages F S (μ := μ) (η := η) (νG := νG)
    (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW hsimple

set_option maxHeartbeats 800000 in
include hνG hνS in
/-- Corrected Theorem 7.3.1.6. The raw Laurent expansion uses complete
pole blocks. At a simple selected pole the block is the single raw
coefficient. The Fourier basis has the individual expansions and estimates
on every finite stage satisfying the manuscript's class group hypothesis. -/
theorem sLocalPrimaryOrbitalBases_corrected
    [Subsingleton (SPicardGroup F S)] (θ : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) :
    let W := sLocalPrimaryPlaces F S p
    let M := sLocalHomogeneousThetaKernel F S ν θ
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν θ) ⧸ R
    let J := SLocalPrimaryEulerJetIndex F S θ p W
    let d := sLocalPrimaryEulerPeriod p
    let t := sLocalSelectedFinitePoleCount F S θ W
    let l := sLocalPoleCount F S θ
    let B (c : ℂ) := ↥(Finset.Ioc (l c - t c) (l c))
    let Z₀ (f : E F S) (z : ℂ) := Z F S μ θ⁻¹ (sLocalFourierCompression F S f) (1-z)
    (Nonempty (ℕ ≃ (Σ c : ℂ, Fin (t c))) ∨
      (IsEmpty (Σ c : ℂ, Fin (t c)) ∧ Subsingleton X)) ∧
    (∃ (x : J × ℤ → X) (D : J × ℤ → StrongDual ℂ X),
      (∀ i f, D i (R.mkQ (M.mkQ f)) = iteratedDeriv i.1.2.val (Z₀ f)
        (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)) ∧
      (∀ i j, D i (x j) = if i = j then 1 else 0) ∧
      (∀ y : X, HasSum (fun i ↦ D i y • x i) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun i ↦ q (D i y • x i)) ∧ (∑' i, q (D i y • x i)) ≤ r y) ∧
      (∀ (q : Seminorm ℂ X), Continuous q → ∀ b e : ℝ,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (i : J × ℤ) (n : ℤ),
          i.1.1.val + (i.2 : ℝ) * d = b + (n : ℝ) * e →
          q (x i) ≤ C * (1 + |(n : ℝ)|)^N) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun i ↦ g (x i) • D i) g) ∧
    (∃ (u : (Σ c : ℂ, B c) → X) (L : (Σ c : ℂ, B c) → StrongDual ℂ X),
      (∀ i f, L i (R.mkQ (M.mkQ f)) = sLocalLaurentCoeff F S (fun v ↦ μ v.val) θ i.1 i.2.val f) ∧
      (∀ i j, L i (u j) = if i = j then 1 else 0) ∧
      let P (c : ℂ) (y : X) := ∑ k : B c, L ⟨c,k⟩ y • u ⟨c,k⟩
      (∀ y : X, HasSum (fun c ↦ P c y) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun c ↦ q (P c y)) ∧ (∑' c, q (P c y)) ≤ r y) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun c ↦ ∑ k : B c, g (u ⟨c,k⟩) • L ⟨c,k⟩) g) ∧
    ∀ (f : E F S) (b e : ℝ), e ≠ 0 → ∀ N k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, |(n : ℝ)|^N *
        ‖iteratedDeriv k (Z₀ f) (((b + (n : ℝ) * e : ℝ) : ℂ) * Complex.I)‖ ≤ C := by
  have hs := sIdeleClassInclusion_surjective_of_trivial_picard F S
  obtain ⟨ω, hu, hθ⟩ := exists_unramified_globalNormOne_for_local F S θ hs
  subst θ
  let W := sLocalPrimaryPlaces F S p
  have hW : W ⊆ sLocalPrimaryPlaces F S p := Finset.Subset.refl _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sLocalPrimaryQuotient_index_enumerable_or_empty F S (fun v ↦ μ v.val)
      ν hνS _ hp hW
  · exact exists_sLocalPrimaryQuotient_compressedFourier_bases F S (μG := μ) (η := η)
      (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  · exact exists_sLocalPrimaryQuotient_polar_blocks_all_stages F S (μ := μ) (η := η)
      (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  · intro f b e he N k
    exact sLocalOrbitalFourierJets_rapid F S (fun v ↦ μ v.val) ν hνS _ f b e he N k

end

end Masullo
