import ElementaryCyclicTails
import BruhatCyclicWeightedRange
import CompactPeriodizationSection
import BruhatCompactSupport

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

section Elementary

variable {d e r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

private theorem elementarySchwartz_cutPeriod_mem
    (l : ElementaryLCAModel d e r F →+ ℝ) (hl : IsProperMap l)
    (s : ElementaryLCAModel d e r F) (hs : 0 < l s)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hbs : support b ⊆ K) (f : ElementarySchwartz d e r F) :
    (fun x ↦ b (l x) * ∑' n : ℤ, f (x + n • s)) ∈ elementarySchwartzSubmodule d e r F := by
  let A := ElementaryLCAModel d e r F
  let g (x : A) := b (l x) * ∑' n : ℤ, f (x + n • s)
  have hc : HasCompactSupport g := HasCompactSupport.intro'
    (hl.isCompact_preimage hK) (hK.isClosed.preimage hl.continuous) fun x hx ↦ by
      have hz : b (l x) = 0 := notMem_support.mp (fun h ↦ hx (hbs h))
      exact (congrArg (· * (∑' n : ℤ, f (x + n • s))) hz).trans (zero_mul _)
  refine elementarySchwartz_mem_of_compactSupport g hc fun a c ↦ ?_
  let X := EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)
  let H := l.comp (elementaryCoverHom : X →+ A)
  have hH : Continuous H := hl.continuous.comp elementaryCoverHom_continuous
  let L := H.toRealLinearMap hH
  have hlog (x : X) : l (elementaryCover x a c) = L x + l (elementaryCover (0 : X) a c) := by
    have he := elementaryCover_add (0 : X) x a c
    rw [zero_add] at he
    rw [he, map_add, add_comm]
    rfl
  have hg : (fun x : X ↦ g (elementaryCover x a c)) =
      fun x : X ↦ b (L x + l (elementaryCover (0 : X) a c)) *
        ∑' n : ℤ, f (elementaryCover x a c + n • s) := by
    funext x
    exact congrArg (fun y ↦ b y * ∑' n : ℤ, f (elementaryCover x a c + n • s)) (hlog x)
  rw [hg]
  exact (hb.comp (L.contDiff.add contDiff_const)).mul
    (elementaryCyclicSeries_smooth id injective_id l hl.continuous s hs f a c).1

end Elementary

include hm in
private theorem exists_wholeStage_cutPeriod
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hbs : support b ⊆ K) (P : WholeBruhatStage G) (f : P.val.Space) :
    ∃ v : P.val.Space, ∀ x, P.val.realize v x =
      b (m x).toAdd * bruhatSchwartz_cyclicOrbitSum m γ hγ x (P.val.inclusion f) := by
  let A := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor
  let l := P.logCoordinate m
  let φ := P.coordinates
  let s : A := (φ γ).toAdd
  have hl := P.logCoordinate_isProperMap m hm
  have hs : 0 < l s := (P.logCoordinate_coordinates m γ).symm ▸ hγ
  have hcoord (x : G) (n : ℤ) : (φ (γ ^ n * x)).toAdd = (φ x).toAdd + n • s := by
    calc
      _ = (φ (γ ^ n) * φ x).toAdd := congrArg Multiplicative.toAdd (φ.map_mul _ _)
      _ = (φ γ ^ n * φ x).toAdd := congrArg (fun y ↦ (y * φ x).toAdd) (φ.map_zpow γ n)
      _ = n • s + (φ x).toAdd := rfl
      _ = _ := add_comm _ _
  let v : P.val.Space := ⟨_, elementarySchwartz_cutPeriod_mem l hl s hs b hb K hK hbs f⟩
  refine ⟨v, fun x ↦ ?_⟩
  have hv (n : ℤ) : f.val ((φ x).toAdd + n • s) = P.val.realize f (γ ^ n * x) :=
    (congrArg f.val (hcoord x n).symm).trans (P.realize_eq_coordinates f (γ ^ n * x)).symm
  exact (P.realize_eq_coordinates v x).trans (congrArg₂ (· * ·)
    (congrArg b (P.logCoordinate_coordinates m x))
    ((tsum_congr hv).trans (bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x (P.val.inclusion f)).symm))

include hm hms in
private theorem exists_stage_factor_of_wholeStage_evaluation
    (A : G → BruhatSchwartz G →L[ℂ] ℂ)
    (hA : ∀ (P : WholeBruhatStage G) (f : P.val.Space), ∃ v : P.val.Space,
      ∀ x, P.val.realize v x = A x (P.val.inclusion f))
    (p : BruhatSchwartzStage G) :
    ∃ (P : WholeBruhatStage G) (T B : p.Space →L[ℂ] P.val.Space),
      (∀ f, P.val.inclusion (T f) = p.inclusion f) ∧
        ∀ f x, P.val.realize (B f) x = A x (p.inclusion f) := by
  obtain ⟨P, hp⟩ := exists_wholeBruhatStage_refinement m hm hms p
  let T := p.transition P.val hp
  have hT (f : p.Space) : P.val.inclusion (T f) = p.inclusion f := p.inclusion_transition P.val hp f
  let a (x : G) : p.Space →L[ℂ] ℂ := (A x).comp p.inclusionCLM
  have ha (f : p.Space) : ∃ g : P.val.Space, ∀ x, P.val.realize g x = a x f := by
    obtain ⟨g, hg⟩ := hA P (T f)
    exact ⟨g, fun x ↦ (hg x).trans (congrArg (A x) (hT f))⟩
  have hB : ∃ B : p.Space →L[ℂ] P.val.Space, ∀ f x, P.val.realize (B f) x = a x f :=
    bruhatStage_exists_clm_of_evaluation p P.val id surjective_id a ha
  exact ⟨P, T, hB.choose, hT, hB.choose_spec⟩

include hm hms in
/-- The logarithmically cut-off orbit sum and its residual lie continuously
in a common whole-group stage for each input stage. -/
theorem exists_bruhatCyclic_cutPeriod_stage
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hbs : support b ⊆ K) (p : BruhatSchwartzStage G) :
    ∃ (P : WholeBruhatStage G) (T B : p.Space →L[ℂ] P.val.Space),
      (∀ f, P.val.inclusion (T f) = p.inclusion f) ∧ ∀ f x,
        P.val.realize (B f) x =
          b (m x).toAdd * bruhatSchwartz_cyclicOrbitSum m γ hγ x (p.inclusion f) :=
  exists_stage_factor_of_wholeStage_evaluation m hm hms
    (fun x ↦ (b (m x).toAdd) • bruhatSchwartz_cyclicOrbitSum m γ hγ x)
    (exists_wholeStage_cutPeriod m hm γ hγ b hb K hK hbs) p

private theorem exists_compactTest_clm_of_stage_values
    (A : G → BruhatSchwartz G →L[ℂ] ℂ) (K : Set G) (hK : IsCompact K)
    (hzero : ∀ f x, x ∉ K → A x f = 0)
    (hStage : ∀ p : BruhatSchwartzStage G, ∃ (q : BruhatSchwartzStage G) (B : p.Space →L[ℂ] q.Space),
      ∀ f x, q.realize (B f) x = A x (p.inclusion f)) :
    ∃ F : BruhatSchwartz G →L[ℂ] BruhatCompactTest G, ∀ f x, (F f).val.val x = A x f := by
  obtain ⟨F, hF⟩ := bruhatSchwartz_exists_clm_of_stage_evaluation id surjective_id A hStage
  have hc (f : BruhatSchwartz G) : F f ∈ bruhatCompactTestSubmodule :=
    HasCompactSupport.intro' hK hK.isClosed fun x hx ↦ (hF f x).trans (hzero f x hx)
  let L : BruhatSchwartz G →ₗ[ℂ] BruhatCompactTest G :=
    BruhatCompactTest.algebraicEquiv.symm.toLinearMap.comp (F.toLinearMap.codRestrict _ hc)
  have hL (f : BruhatSchwartz G) (x : G) : (L f).val.val x = A x f := hF f x
  refine ⟨⟨L, (locallyConvexFinal_continuous_iff
    (fun p : BruhatSchwartzStage G ↦ p.inclusion) L).2 fun p ↦ ?_⟩, hL⟩
  obtain ⟨q, B, hB⟩ := hStage p
  let j : BruhatCompactTestIndex G := ⟨q, ⟨K, hK⟩⟩
  have hB' (f : p.Space) : B f ∈ q.compactTests K :=
    fun x hx ↦ (hB f x).trans (hzero (p.inclusion f) x hx)
  let C : p.Space →L[ℂ] j.Space := B.codRestrict _ hB'
  have he : (L.comp p.inclusion : p.Space → BruhatCompactTest G) = j.inclusionCLM ∘ C := by
    funext f
    apply BruhatCompactTest.val_injective
    exact Subtype.ext (funext fun x ↦ (hL (p.inclusion f) x).trans (hB f x).symm)
  rw [he]
  exact j.inclusionCLM.continuous.comp C.continuous

include hm hms in
private theorem exists_bruhatCyclic_cutPeriod
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K) (hbs : support b ⊆ K) :
    ∃ F : BruhatSchwartz G →L[ℂ] BruhatCompactTest G, ∀ f x,
      (F f).val.val x = b (m x).toAdd * bruhatSchwartz_cyclicOrbitSum m γ hγ x f := by
  let A (x : G) : BruhatSchwartz G →L[ℂ] ℂ :=
    (b (m x).toAdd) • bruhatSchwartz_cyclicOrbitSum m γ hγ x
  let K' : Set G := (fun x : G ↦ (m x).toAdd) ⁻¹' K
  have hK' : IsCompact K' := hm.isCompact_preimage (show IsCompact (Multiplicative.toAdd ⁻¹' K) from hK)
  have hzero (f : BruhatSchwartz G) (x : G) (hx : x ∉ K') : A x f = 0 := by
    have hz : b (m x).toAdd = 0 := notMem_support.mp (fun h ↦ hx (hbs h))
    exact (congrArg (· * bruhatSchwartz_cyclicOrbitSum m γ hγ x f) hz).trans (zero_mul _)
  refine exists_compactTest_clm_of_stage_values A K' hK' hzero fun p ↦ ?_
  obtain ⟨q, _, B, _, hB⟩ := exists_bruhatCyclic_cutPeriod_stage m hm hms γ hγ b hb K hK hbs p
  exact ⟨q.val, B, hB⟩

/-- The pointwise norm-one character equation on a test function. -/
def CyclicNormOneIsotypic (m : G →ₜ* Multiplicative ℝ) (w : PontryaginDual m.toMonoidHom.ker)
    (f : G → ℂ) : Prop :=
  ∀ (a : m.toMonoidHom.ker) x, f (a.val⁻¹ * x) = (w a : ℂ) * f x

include hm hms hγ in
/-- A logarithmic cutoff gives a continuously split cyclic difference and
a representative supported in a prescribed compact window. -/
theorem exists_bruhatCyclic_split_of_cover
    (K : Set ℝ) (hK : IsCompact K)
    (hcov : ∀ x : ℝ, ∃ n : ℤ, x + (m γ).toAdd * (n : ℝ) ∈ interior K)
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ (S : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
      (D : BruhatSchwartz G →L[ℂ] BruhatSchwartz G),
      (∀ f, bruhatSchwartzDifference γ (D f) = f - modulatedDecay_zeroInclusion m I h0 (S f)) ∧
      (∀ f, support (S f).val ⊆ (fun x ↦ (m x).toAdd) ⁻¹' K) ∧
      ∀ w f, CyclicNormOneIsotypic m w f.val →
        CyclicNormOneIsotypic m w (S f).val ∧ CyclicNormOneIsotypic m w (D f).val := by
  let d := (m γ).toAdd
  obtain ⟨b, hb, hbs, hper⟩ := integerPeriodization_extends_periodic hK hγ hcov
  obtain ⟨F, hF⟩ := exists_bruhatCyclic_cutPeriod m hm hms γ hγ b hb K hK hbs
  let T : BruhatCompactTest G →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨bruhatCompactTest_toModulatedExponentialInductive m I,
      bruhatCompactTest_continuous_inductiveDecay m I hm hms⟩
  let J := modulatedDecay_zeroInclusion m I h0
  let S := T.comp F
  letI : IsTopologicalAddGroup (BruhatSchwartz G) :=
    (PolynormableSpace.withSeminorms ℂ _).topologicalAddGroup
  let M := ContinuousLinearMap.id ℂ (BruhatSchwartz G) - J.comp S
  have hJS (f : BruhatSchwartz G) (x : G) :
      (J (S f)).val x = b (m x).toAdd * bruhatSchwartz_cyclicOrbitSum m γ hγ x f := hF f x
  have hM (f : BruhatSchwartz G) (x : G) :
      bruhatSchwartz_cyclicOrbitSum m γ hγ x (M f) = 0 := by
    let A := bruhatSchwartz_cyclicOrbitSum m γ hγ
    have hlog (n : ℤ) : (m (γ ^ n * x)).toAdd = (m x).toAdd + d * (n : ℝ) := by
      simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul, d]
      ring
    have hcut : A x (J (S f)) = A x f := calc
      _ = ∑' n : ℤ, (J (S f)).val (γ ^ n * x) := bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x _
      _ = ∑' n : ℤ, b ((m x).toAdd + d * (n : ℝ)) * A x f :=
        tsum_congr fun n ↦ (hJS f _).trans (congrArg₂ (· * ·) (congrArg b (hlog n))
          (bruhatSchwartz_cyclicOrbitSum_zpow m γ hγ x n f))
      _ = _ := congrFun (hper (fun _ : ℝ ↦ A x f) (fun _ ↦ rfl)) (m x).toAdd
    change A x (f - J (S f)) = 0
    rw [map_sub, hcut, sub_self]
  have hStage (p : BruhatSchwartzStage G) :
      ∃ (Q : WholeBruhatStage G) (V : p.Space →L[ℂ] Q.val.Space),
        ∀ f, Q.val.inclusion (V f) = M (p.inclusion f) := by
    obtain ⟨q, U, B, hU, hB⟩ := exists_bruhatCyclic_cutPeriod_stage m hm hms γ hγ b hb K hK hbs p
    refine ⟨q, U - B, fun f ↦ Subtype.ext (funext fun x ↦ ?_)⟩
    have hx := congrArg (fun u : BruhatSchwartz G ↦ u.val x) (hU f)
    change q.val.realize (U f - B f) x = (p.inclusion f).val x - (J (S (p.inclusion f))).val x
    exact (congrFun (q.val.realize.map_sub (U f) (B f)) x).trans
      (congrArg₂ (· - ·) hx ((hB f x).trans (hJS (p.inclusion f) x).symm))
  obtain ⟨D, hD, hTail⟩ := exists_bruhatSchwartz_cyclicDivision m hm γ hγ M hM hStage
  refine ⟨S, D, hD, ?_, fun w f hf ↦ ?_⟩
  · intro f x hx
    by_contra hx'
    have hz : b (m x).toAdd = 0 := notMem_support.mp fun h ↦ hx' (hbs h)
    exact hx ((hJS f x).trans (by rw [hz, zero_mul]))
  have hSiso : CyclicNormOneIsotypic m w (S f).val := by
    intro a x
    have ha : m a.val = 1 := a.property
    have hlog : (m (a.val⁻¹ * x)).toAdd = (m x).toAdd := by rw [map_mul, map_inv, ha, inv_one, one_mul]
    have hsum : bruhatSchwartz_cyclicOrbitSum m γ hγ (a.val⁻¹ * x) f =
        (w a : ℂ) * bruhatSchwartz_cyclicOrbitSum m γ hγ x f := by
      simp only [bruhatSchwartz_cyclicOrbitSum_apply, ← tsum_mul_left]
      exact tsum_congr fun n ↦ (congrArg f.val (mul_left_comm _ _ _)).trans (hf a _)
    change (J (S f)).val (a.val⁻¹ * x) = (w a : ℂ) * (J (S f)).val x
    rw [hJS, hJS, hlog, hsum, mul_left_comm]
  refine ⟨hSiso, fun a x ↦ ?_⟩
  have hMiso : CyclicNormOneIsotypic m w (M f).val := by
    intro a y
    change f.val (a.val⁻¹ * y) - (S f).val (a.val⁻¹ * y) =
      (w a : ℂ) * (f.val y - (S f).val y)
    exact (congrArg₂ (· - ·) (hf a y) (hSiso a y)).trans (mul_sub _ _ _).symm
  rw [hTail, hTail, bruhatSchwartz_cyclicForwardSum_apply, bruhatSchwartz_cyclicForwardSum_apply, ← tsum_mul_left]
  exact tsum_congr fun n ↦ (congrArg (M f).val (mul_left_comm _ _ _)).trans (hMiso a _)

include hm hms hγ in
/-- A fixed logarithmic cutoff and the forward orbit tail continuously split
the ordinary cyclic difference, with a representative in the decay space. -/
theorem exists_bruhatCyclic_split (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ (S : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
      (D : BruhatSchwartz G →L[ℂ] BruhatSchwartz G),
      (∀ f, bruhatSchwartzDifference γ (D f) = f - modulatedDecay_zeroInclusion m I h0 (S f)) ∧
      ∀ w f, CyclicNormOneIsotypic m w f.val →
        CyclicNormOneIsotypic m w (S f).val ∧ CyclicNormOneIsotypic m w (D f).val := by
  have hcov (x : ℝ) : ∃ n : ℤ,
      x + (m γ).toAdd * (n : ℝ) ∈ interior (Icc 0 (2 * (m γ).toAdd)) := by
    rw [interior_Icc]
    exact openInterval_covers_integerTranslations hγ (by linarith) x
  obtain ⟨S, D, hSD, _, hIso⟩ :=
    exists_bruhatCyclic_split_of_cover m hm hms γ hγ _ isCompact_Icc hcov I h0
  exact ⟨S, D, hSD, hIso⟩


end

end Masullo
