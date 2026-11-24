import BruhatWholeQuotientStages
import BruhatStageEvaluation
import ElementaryCyclicPeriodization
import BruhatCyclicWeightedRange
import ModulatedCharacters
import CompactPeriodizationSection

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Γ" => Subgroup.zpowers γ
local notation "H" => G ⧸ Γ

variable [hT : T2Space (G ⧸ Subgroup.zpowers γ)]
  [hLC : LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

include hm hms hT hLC in
/-- The logarithmic cutoff pullback takes each whole-group quotient stage
continuously into a single whole-group source stage. -/
theorem exists_bruhatCyclic_cutoff_stageCLM
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hs : support b ⊆ K) (Q : WholeBruhatStage H) :
    ∃ (P : WholeBruhatStage G) (L : Q.val.Space →L[ℂ] P.val.Space),
      ∀ f x, P.val.realize (L f) x = b (m x).toAdd * Q.val.realize f (QuotientGroup.mk x) := by
  have hΓ : IsClosed (Γ : Set G) := by
    rw [← QuotientGroup.preimage_mk_one Γ]
    exact isClosed_singleton.preimage QuotientGroup.continuous_mk
  have hLift : ∃ P : WholeBruhatStage G,
      P.val.1.kernel ≤ Q.val.1.kernel.comap (QuotientGroup.mk' Γ) :=
    exists_wholeBruhatStage_quotient_pullback Γ hΓ m hm hms Q
  let P : WholeBruhatStage G := hLift.choose
  have hp : P.val.1.kernel ≤ Q.val.1.kernel.comap (QuotientGroup.mk' Γ) := hLift.choose_spec
  let q : G →ₜ* H := ⟨QuotientGroup.mk' Γ, QuotientGroup.continuous_mk⟩
  let ψ := P.coordinateMap Q q hp
  let φ := ψ.toMonoidHom.toAdditive
  let l := P.logCoordinate m
  let U (f : Q.val.Space) : P.val.Space := ⟨_, elementarySchwartz_logCutoff_pullback_mem l
    (P.logCoordinate_isProperMap m hm) b hb K hK hs φ ψ.continuous f⟩
  let L : Q.val.Space →ₗ[ℂ] P.val.Space :=
    { toFun := U
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ mul_add _ _ _)
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ mul_left_comm _ _ _) }
  have hval (f : Q.val.Space) (x : G) :
      P.val.realize (L f) x = b (m x).toAdd * Q.val.realize f (QuotientGroup.mk x) := by
    have hco : (ψ (P.coordinates x)).toAdd = (Q.coordinates (q x)).toAdd :=
      congrArg Multiplicative.toAdd (P.coordinateMap_coordinates Q q hp x)
    calc
      P.val.realize (L f) x = b (l (P.coordinates x).toAdd) * f.val (ψ (P.coordinates x)).toAdd :=
        P.realize_eq_coordinates (L f) x
      _ = b (m x).toAdd * f.val (Q.coordinates (q x)).toAdd :=
        congrArg₂ (fun t y ↦ b t * f.val y) (P.logCoordinate_coordinates m x) hco
      _ = _ := congrArg (b (m x).toAdd * ·) ((Q.realize_eq_coordinates f (q x)).symm)
  refine ⟨P, ⟨L, bruhatStage_continuous_of_evaluation _ _ L fun x ↦ ?_⟩, hval⟩
  rw [funext (fun f ↦ hval f x)]
  exact continuous_const.mul
    ((bruhatSchwartz_continuous_eval (QuotientGroup.mk x)).comp Q.val.inclusionCLM.continuous)

include hm hms hγ hT hLC in
/-- Multiplication by a compact logarithmic cutoff lifts any compact
quotient Schwartz test to a compactly supported Schwartz–Bruhat test. -/
theorem exists_bruhatCyclic_cutoff_lift
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hs : support b ⊆ K) (g : BruhatSchwartz H) :
    ∃ f : BruhatSchwartz G, HasCompactSupport f.val ∧
      ∀ x, f.val x = b (m x).toAdd * g.val (QuotientGroup.mk x) := by
  letI : CompactSpace H := modulatedCyclicQuotient_compact m hm γ hγ
  obtain ⟨p, v, hv⟩ := g.property
  obtain ⟨Q, hpQ⟩ := exists_wholeBruhatStage_refinement_of_compact p
  let v' := p.transition Q.val hpQ v
  have hv' : Q.val.realize v' = g.val :=
    (congrArg Subtype.val (p.inclusion_transition Q.val hpQ v)).trans hv
  obtain ⟨P, L, hL⟩ := exists_bruhatCyclic_cutoff_stageCLM m hm hms γ b hb K hK hs Q
  let f := P.val.inclusion (L v')
  have hval (x : G) : f.val x = b (m x).toAdd * g.val (QuotientGroup.mk x) := by
    change P.val.realize (L v') x = _
    simpa only [hv'] using hL v' x
  refine ⟨f, HasCompactSupport.intro' (hm.isCompact_preimage hK) ?_ ?_, hval⟩
  · exact hK.isClosed.preimage (continuous_toAdd.comp m.continuous)
  · intro x hx
    rw [hval]
    have he : b (m x).toAdd = 0 := by
      by_contra h
      exact hx (hs h)
    rw [he, zero_mul]

/-- Pullback followed by a compact logarithmic cutoff is continuous on
the full quotient Schwartz–Bruhat space, with values in the compact-test topology. -/
def bruhatCyclicCompactCutoffLift
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hs : support b ⊆ K) : BruhatSchwartz H →L[ℂ] BruhatCompactTest G := by
  classical
  letI : CompactSpace H := modulatedCyclicQuotient_compact m hm γ hγ
  let F (g : BruhatSchwartz H) := (exists_bruhatCyclic_cutoff_lift m hm hms γ hγ b hb K hK hs g).choose
  have hF (g : BruhatSchwartz H) (x : G) :=
    (exists_bruhatCyclic_cutoff_lift m hm hms γ hγ b hb K hK hs g).choose_spec.2 x
  let L : BruhatSchwartz H →ₗ[ℂ] BruhatCompactTest G :=
    { toFun := fun g ↦ BruhatCompactTest.algebraicEquiv.symm
        ⟨F g, (exists_bruhatCyclic_cutoff_lift m hm hms γ hγ b hb K hK hs g).choose_spec.1⟩
      map_add' := fun f g ↦ BruhatCompactTest.val_injective (Subtype.ext (funext fun x ↦ by
        change (F (f + g)).val x = (F f).val x + (F g).val x
        rw [hF, hF, hF]
        exact mul_add _ _ _))
      map_smul' := fun c f ↦ BruhatCompactTest.val_injective (Subtype.ext (funext fun x ↦ by
        change (F (c • f)).val x = c * (F f).val x
        rw [hF, hF]
        exact mul_left_comm _ _ _)) }
  refine ⟨L, (locallyConvexFinal_continuous_iff
    (fun p : BruhatSchwartzStage H ↦ p.inclusion) L).2 fun p ↦ ?_⟩
  obtain ⟨Q, hp⟩ := exists_wholeBruhatStage_refinement_of_compact p
  obtain ⟨P, A, hA⟩ := exists_bruhatCyclic_cutoff_stageCLM m hm hms γ b hb K hK hs Q
  let K' : Set G := (fun x : G ↦ (m x).toAdd) ⁻¹' K
  have hK' : IsCompact K' := hm.isCompact_preimage (show IsCompact (Multiplicative.toAdd ⁻¹' K) from hK)
  have hA' (f : Q.val.Space) : A f ∈ P.val.compactTests K' := by
    intro x hx
    have hz : b (m x).toAdd = 0 := by
      by_contra h
      exact hx (hs h)
    exact (hA f x).trans ((congrArg (· * Q.val.realize f (QuotientGroup.mk x)) hz).trans (zero_mul _))
  let j : BruhatCompactTestIndex G := ⟨P.val, ⟨K', hK'⟩⟩
  let A' : Q.val.Space →L[ℂ] j.Space := A.codRestrict (P.val.compactTests K') hA'
  have he : (L.comp p.inclusion : p.Space → BruhatCompactTest G) =
      j.inclusionCLM ∘ A' ∘ p.transition Q.val hp := by
    funext f
    apply BruhatCompactTest.val_injective
    apply Subtype.ext
    funext x
    change (F (p.inclusion f)).val x = P.val.realize (A (p.transition Q.val hp f)) x
    exact (hF (p.inclusion f) x).trans
      ((congrArg (fun u : BruhatSchwartz H ↦ b (m x).toAdd * u.val (QuotientGroup.mk x))
        (p.inclusion_transition Q.val hp f).symm).trans ((hA (p.transition Q.val hp f) x).symm))
  rw [he]
  exact j.inclusionCLM.continuous.comp (A'.continuous.comp (p.transition Q.val hp).continuous)

/-- The ordinary Schwartz–Bruhat realization of a cyclic compact cutoff lift. -/
def bruhatCyclicCutoffLift
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hs : support b ⊆ K) : BruhatSchwartz H →L[ℂ] BruhatSchwartz G :=
  bruhatCompactTest_toSchwartz.comp (bruhatCyclicCompactCutoffLift m hm hms γ hγ b hb K hK hs)

/-- A cyclic compact cutoff lift takes values continuously in every decay space. -/
def bruhatCyclicDecayCutoffLift (I : Set ℝ)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hs : support b ⊆ K) : BruhatSchwartz H →L[ℂ] ModulatedExponentialInductive m I :=
  (⟨bruhatCompactTest_toModulatedExponentialInductive m I,
    bruhatCompactTest_continuous_inductiveDecay m I hm hms⟩ :
    BruhatCompactTest G →L[ℂ] ModulatedExponentialInductive m I).comp
      (bruhatCyclicCompactCutoffLift m hm hms γ hγ b hb K hK hs)

theorem bruhatCyclicCutoffLift_apply
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K)
    (hs : support b ⊆ K) (g : BruhatSchwartz H) (x : G) :
    (bruhatCyclicCutoffLift m hm hms γ hγ b hb K hK hs g).val x =
      b (m x).toAdd * g.val (QuotientGroup.mk x) :=
  (exists_bruhatCyclic_cutoff_lift m hm hms γ hγ b hb K hK hs g).choose_spec.2 x

include hm hms hγ hT hLC in
/-- Every test on the actual cyclic quotient has a compactly supported
Schwartz–Bruhat lift under the cyclic orbit sums. -/
theorem exists_bruhatCyclic_compact_periodization_lift (g : BruhatSchwartz H) :
    ∃ f : BruhatSchwartz G, HasCompactSupport f.val ∧
      ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = g.val (QuotientGroup.mk x) := by
  let d := (m γ).toAdd
  let K := Icc 0 (2 * d)
  have hK : IsCompact K := isCompact_Icc
  have hcov (x : ℝ) : ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K := by
    change ∃ n : ℤ, x + d * (n : ℝ) ∈ interior (Icc 0 (2 * d))
    rw [interior_Icc]
    exact openInterval_covers_integerTranslations hγ (by dsimp [d]; linarith) x
  obtain ⟨b, hb, hbs, hper⟩ := integerPeriodization_extends_periodic hK hγ hcov
  obtain ⟨f, hf, hval⟩ := exists_bruhatCyclic_cutoff_lift m hm hms γ hγ b hb K hK hbs g
  refine ⟨f, hf, fun x ↦ ?_⟩
  rw [bruhatSchwartz_cyclicOrbitSum_apply]
  have hlog (n : ℤ) : (m (γ ^ n * x)).toAdd = (m x).toAdd + d * (n : ℝ) := by
    simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul, d]
    ring
  have hq (n : ℤ) : (QuotientGroup.mk (γ ^ n * x) : H) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (Subgroup.zpow_mem_zpowers γ n), one_mul]
  simp_rw [hval, hlog, hq]
  exact congrFun (hper (fun _ : ℝ ↦ g.val (QuotientGroup.mk x)) (fun _ ↦ rfl)) (m x).toAdd

include hm hms hT hLC in
/-- The compact lifts also give surjectivity of the orbit-sum construction
from the actual entire exponential-decay space. -/
theorem exists_bruhatCyclic_entireDecay_periodization_lift (g : BruhatSchwartz H) :
    ∃ f : ModulatedExponentialInductive m (univ : Set ℝ), HasCompactSupport f.val ∧
      ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x
        (modulatedDecay_zeroInclusion m univ (mem_univ 0) f) = g.val (QuotientGroup.mk x) := by
  obtain ⟨u, hu, h⟩ := exists_bruhatCyclic_compact_periodization_lift m hm hms γ hγ g
  have hmem : u.val ∈ modulatedExponentialDecaySubmodule m (univ : Set ℝ) :=
    modulatedExponentialDecay_mem_of_smooth_compactSupport m univ
      (bruhatSchwartz_le_smooth u.property) hu
  let f : ModulatedExponentialInductive m (univ : Set ℝ) :=
    ModulatedExponentialInductive.algebraicEquiv.symm ⟨u.val, hmem⟩
  have hu' : modulatedDecay_zeroInclusion m univ (mem_univ 0) f = u := Subtype.ext rfl
  exact ⟨f, hu, fun x ↦ by rw [hu']; exact h x⟩

end

end Masullo
