import BruhatIsotypeComparison
import BruhatSobolevConvolution
import ModulatedCharacters
import ModulatedExponentialInductive
import FrechetFactorization

open Filter Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

set_option maxHeartbeats 1600000

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

section Restriction

variable {m : G →ₜ* Multiplicative ℝ}
  (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)

local notation "S" => BruhatSchwartz G

private def stageRadialDerivative (P : BruhatSchwartzStage G) : P.Space →L[ℂ] P.Space :=
  elementarySchwartz_derivative ((P.1.stageCoordinates P.2).comp (P.1.restrictOneParameter τ))

private theorem hasDerivAt_stageRadialProfile (P : BruhatSchwartzStage G) (f : P.Space) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ P.realize f (τ (Multiplicative.ofAdd t)))
      (P.realize (stageRadialDerivative τ P f) (τ (Multiplicative.ofAdd x))) x := by
  let c := (P.1.stageCoordinates P.2).comp (P.1.restrictOneParameter τ)
  have hz (t : ℝ) : P.realize f (τ (Multiplicative.ofAdd t)) = f (c (Multiplicative.ofAdd t)).toAdd :=
    P.1.realizeSchwartz_apply_of_mem P.2 f ⟨_, P.1.oneParameter_mem_upper τ t⟩
  have hD (t : ℝ) :
      P.realize (stageRadialDerivative τ P f) (τ (Multiplicative.ofAdd t)) =
        elementaryOrbitDeriv c f (c (Multiplicative.ofAdd t)).toAdd :=
    P.1.realizeSchwartz_apply_of_mem P.2 _ ⟨_, P.1.oneParameter_mem_upper τ t⟩
  rw [hD]
  let F (t : ℝ) := f ((c (Multiplicative.ofAdd x)).toAdd + (c (Multiplicative.ofAdd t)).toAdd)
  let d := elementaryOrbitDeriv c f (c (Multiplicative.ofAdd x)).toAdd
  have h : HasDerivAt F d 0 := elementaryOrbit_hasDerivAt c f
    (fun a b ↦ (f.property.1 a b).differentiable (by simp)) (c (Multiplicative.ofAdd x)).toAdd
  let H (t : ℝ) := t - x
  have hH : HasDerivAt H 1 x := (hasDerivAt_id' x).sub_const x
  have hc := h.scomp_of_eq x hH (show (0 : ℝ) = H x by simp [H])
  rw [one_smul] at hc
  have hEq : F ∘ H = (fun t : ℝ ↦ P.realize f (τ (Multiplicative.ofAdd t))) := by
    funext t
    change f ((c (Multiplicative.ofAdd x)).toAdd + (c (Multiplicative.ofAdd (t - x))).toAdd) = _
    rw [hz, ← show Multiplicative.ofAdd x * Multiplicative.ofAdd (t - x) =
      Multiplicative.ofAdd t from congrArg Multiplicative.ofAdd (show x + (t - x) = t by ring), map_mul]
    rfl
  rwa [hEq] at hc

private def stageRadialDerivativeIterate (P : BruhatSchwartzStage G) :
    ℕ → (P.Space →L[ℂ] P.Space)
  | 0 => ContinuousLinearMap.id ℂ P.Space
  | n + 1 => (stageRadialDerivative τ P).comp (stageRadialDerivativeIterate P n)

private theorem iteratedDeriv_stageRadialProfile (P : BruhatSchwartzStage G) (n : ℕ) (f : P.Space) :
    iteratedDeriv n (fun t : ℝ ↦ P.realize f (τ (Multiplicative.ofAdd t))) =
      fun t ↦ P.realize ((stageRadialDerivativeIterate τ P n) f) (τ (Multiplicative.ofAdd t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x ↦ (hasDerivAt_stageRadialProfile τ P (stageRadialDerivativeIterate τ P n f) x).deriv

private theorem stageRadialProfile_smooth (P : BruhatSchwartzStage G) (f : P.Space) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ P.realize f (τ (Multiplicative.ofAdd t))) := by
  apply contDiff_infty.mpr
  intro n
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro k _
    rw [iteratedDeriv_stageRadialProfile]
    exact (bruhatSchwartz_continuous (P.inclusion ((stageRadialDerivativeIterate τ P k) f))).comp
      (τ.continuous.comp continuous_ofAdd)
  · intro k _ x
    rw [iteratedDeriv_stageRadialProfile]
    exact (hasDerivAt_stageRadialProfile τ P ((stageRadialDerivativeIterate τ P k) f) x).differentiableAt

variable [SecondCountableTopology G]

private theorem norm_pow_le_radialWeight (x : ℝ) (k : ℕ) :
    ‖x‖ ^ k ≤ (1 + x ^ 2) ^ k := by
  rw [Real.norm_eq_abs]
  apply pow_le_pow_left₀ (abs_nonneg _) _ _
  nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]

private def stageRadialProfile (P : BruhatSchwartzStage G) (f : P.Space) : 𝓢(ℝ, ℂ) :=
  ⟨_, stageRadialProfile_smooth τ P f, fun k n ↦ by
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    obtain ⟨q, _, hq⟩ := exists_bruhatStage_logWeight_seminorm m P k
    let F := (stageRadialDerivativeIterate τ P n) f
    refine ⟨q F, fun x ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_stageRadialProfile]
    have hx : modulatedLog m (τ (Multiplicative.ofAdd x)) = x :=
      congrArg Multiplicative.toAdd (hτ (Multiplicative.ofAdd x))
    exact (mul_le_mul_of_nonneg_right (norm_pow_le_radialWeight x k) (norm_nonneg _)).trans
      (by simpa only [hx] using hq F (τ (Multiplicative.ofAdd x)))⟩

private theorem stageRadialProfile_seminorm (P : BruhatSchwartzStage G) (k n : ℕ) :
    ∃ q : Seminorm ℂ P.Space, Continuous q ∧ ∀ f,
      SchwartzMap.seminorm ℂ k n (stageRadialProfile τ hτ P f) ≤ q f := by
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  obtain ⟨q, hcont, hq⟩ := exists_bruhatStage_logWeight_seminorm m P k
  let D := stageRadialDerivativeIterate τ P n
  refine ⟨q.comp D.toLinearMap, hcont.comp D.continuous, fun f ↦ ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (apply_nonneg _ _)
  intro x
  change ‖x‖ ^ k * ‖iteratedDeriv n (fun t ↦ P.realize f (τ (Multiplicative.ofAdd t))) x‖ ≤ q (D f)
  rw [iteratedDeriv_stageRadialProfile]
  have hx : modulatedLog m (τ (Multiplicative.ofAdd x)) = x :=
    congrArg Multiplicative.toAdd (hτ (Multiplicative.ofAdd x))
  exact (mul_le_mul_of_nonneg_right (norm_pow_le_radialWeight x k) (norm_nonneg _)).trans
    (by simpa only [hx] using hq (D f) (τ (Multiplicative.ofAdd x)))

include hτ in
private theorem exists_radialRestriction (f : S) :
    ∃ p : 𝓢(ℝ, ℂ), ∀ x, p x = f.val (τ (Multiplicative.ofAdd x)) := by
  obtain ⟨P, u, hu⟩ := f.property
  exact ⟨stageRadialProfile τ hτ P u, fun x ↦ congrFun hu _⟩

/-- Restriction along the logarithmic modulus section is a continuous map
from Schwartz–Bruhat tests to the real Schwartz space. -/
def bruhatSchwartz_radialRestriction : S →L[ℂ] 𝓢(ℝ, ℂ) := by
  let h := exists_radialRestriction τ hτ
  let L : S →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
    { toFun := fun f ↦ (h f).choose
      map_add' f g := SchwartzMap.ext fun x ↦ by
        simp only [(h (f + g)).choose_spec x, add_apply, (h f).choose_spec x,
          (h g).choose_spec x]
        rfl
      map_smul' c f := SchwartzMap.ext fun x ↦ by
        simp only [(h (c • f)).choose_spec x, RingHom.id_apply, smul_apply,
          (h f).choose_spec x]
        rfl }
  letI : PolynormableSpace ℂ 𝓢(ℝ, ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  refine ⟨L, (locallyConvexFinal_continuous_iff (fun P : BruhatSchwartzStage G ↦ P.inclusion) L).mpr ?_⟩
  intro P
  apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
  rintro ⟨k, n⟩
  obtain ⟨q, hq, hqf⟩ := stageRadialProfile_seminorm τ hτ P k n
  apply Seminorm.continuous_of_le hq
  intro f
  have he : L (P.inclusion f) = stageRadialProfile τ hτ P f :=
    SchwartzMap.ext fun x ↦ (h (P.inclusion f)).choose_spec x
  change SchwartzMap.seminorm ℂ k n (L (P.inclusion f)) ≤ q f
  rw [he]
  exact hqf f

theorem bruhatSchwartz_radialRestriction_apply (f : S) (x : ℝ) :
    bruhatSchwartz_radialRestriction τ hτ f x = f.val (τ (Multiplicative.ofAdd x)) := by
  change (exists_radialRestriction τ hτ f).choose x = _
  exact (exists_radialRestriction τ hτ f).choose_spec x

end Restriction

section Extension

private def elementaryRadialCharacter
    {d n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (l : ElementaryLCAModel d n r F →+ ℝ) (hl : IsProperMap l)
    (χ : PontryaginDual (Multiplicative (ElementaryLCAModel d n r F))) :
    𝓢(ℝ, ℂ) →L[ℂ] ElementarySchwartz d n r F := by
  let E := ElementarySchwartz d n r F
  let L : 𝓢(ℝ, ℂ) →ₗ[ℂ] E :=
    { toFun := fun f ↦ ⟨_, elementarySchwartz_radialCharacter_mem l hl χ f⟩
      map_add' f g := Subtype.ext (funext fun x ↦ add_mul _ _ _)
      map_smul' c f := Subtype.ext (funext fun x ↦ mul_assoc _ _ _) }
  refine ⟨L, ?_⟩
  let W := elementarySchwartz_withSeminorms (m := d) (n := n) (r := r) (F := F)
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : FirstCountableTopology E := W.firstCountableTopology
  letI : CompleteSpace E := completeSpace_elementarySchwartz
  letI : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  apply frechet_continuous_of_closed_graph
  have heq : (L.graph : Set (𝓢(ℝ, ℂ) × E)) =
      ⋂ x : ElementaryLCAModel d n r F, {p | p.2 x = p.1 (l x) * (χ (Multiplicative.ofAdd x) : ℂ)} := by
    ext p
    change p.2 = L p.1 ↔ _
    constructor
    · intro hp
      exact mem_iInter.mpr fun x ↦ congrArg (fun f : E ↦ f x) hp
    · intro hp
      exact Subtype.ext (funext fun x ↦ mem_iInter.mp hp x)
  rw [heq]
  apply isClosed_iInter
  intro x
  obtain ⟨z, hz⟩ := elementaryCover_surjective x.2.2.1 x.2.2.2 x.1 x.2.1
  have he : Continuous (fun f : E ↦ f x) := by
    obtain ⟨C, hC⟩ := elementaryPartial_evaluation_continuousLinear
      (m := d) (n := n) (r := r) (F := F) 0 0 (x.1, z) x.2.2.1 x.2.2.2
    exact C.continuous.congr (fun f ↦ by rw [hC, elementaryPartial_zero, hz])
  exact isClosed_eq (he.comp continuous_snd)
    (((BoundedContinuousFunction.evalCLM ℂ (l x)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).continuous.comp continuous_fst |>.mul_const _)

private theorem elementaryRadialCharacter_apply
    {d n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (l : ElementaryLCAModel d n r F →+ ℝ) (hl : IsProperMap l)
    (χ : PontryaginDual (Multiplicative (ElementaryLCAModel d n r F)))
    (f : 𝓢(ℝ, ℂ)) (x : ElementaryLCAModel d n r F) :
    elementaryRadialCharacter l hl χ f x = f (l x) * (χ (Multiplicative.ofAdd x) : ℂ) := rfl

/-- Pullback along the modulus followed by multiplication by a unitary
character is continuous on real Schwartz profiles. The whole image lies
in a single elementary stage on which the character descends. -/
theorem exists_wholeBruhatStage_radialCharacter (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m) (χ : PontryaginDual G) :
    ∃ P : WholeBruhatStage G, ∃ L : 𝓢(ℝ, ℂ) →L[ℂ] P.val.Space,
      ∀ f g, P.val.realize (L f) g = f (m g).toAdd * (χ g : ℂ) := by
  obtain ⟨P, hP, hχ⟩ := exists_modulatedBruhat_character_stage m hm hms χ
  obtain ⟨p⟩ := P.quotient_elementary
  let A := ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor
  let e : Multiplicative A →ₜ* P.StageQuotient := p.equiv.symm
  let lM := (P.descendHom m (P.modulation_eq_one_on_kernel m)).comp e
  let l : A →+ ℝ := lM.toMonoidHom.toAdditive
  have hl : IsProperMap l := (P.descendModulation_isProperMap m hm).comp
    p.equiv.symm.toHomeomorph.isProperMap
  let ψ : PontryaginDual (Multiplicative A) :=
    (P.descendHom (show CircleCharacter G from χ) hχ).comp e
  let Q : BruhatSchwartzStage G := ⟨P, p⟩
  refine ⟨⟨Q, hP⟩, elementaryRadialCharacter l hl ψ, fun f g ↦ ?_⟩
  let x : P.upper.val := ⟨g, hP.symm ▸ Subgroup.mem_top g⟩
  change P.realizeSchwartz p (elementaryRadialCharacter l hl ψ f) x.val = _
  rw [P.realizeSchwartz_apply_of_mem, elementaryRadialCharacter_apply]
  change f ((P.descendHom m (P.modulation_eq_one_on_kernel m))
    (p.equiv.symm (p.equiv (QuotientGroup.mk x)))).toAdd *
    ((P.descendHom (show CircleCharacter G from χ) hχ)
    (p.equiv.symm (p.equiv (QuotientGroup.mk x))) : ℂ) = _
  rw [p.equiv.symm_apply_apply, P.descendHom_mk]
  rfl


/-- Pullback along the modulus followed by multiplication by a unitary
character is continuous into the full Schwartz–Bruhat space. -/
theorem exists_bruhatSchwartz_radialCharacter (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m) (χ : PontryaginDual G) :
    ∃ L : 𝓢(ℝ, ℂ) →L[ℂ] BruhatSchwartz G,
      ∀ f g, (L f).val g = f (m g).toAdd * (χ g : ℂ) := by
  obtain ⟨P, L, hL⟩ := exists_wholeBruhatStage_radialCharacter m hm hms χ
  exact ⟨P.val.inclusionCLM.comp L, hL⟩

end Extension

section Isotype

variable [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G)
  (hτ : ∀ t, m (τ t) = t) (w : PontryaginDual m.toMonoidHom.ker)

local notation "S" => BruhatSchwartz G
local notation "K" => m.toMonoidHom.ker
local notation "χ" => extendModulatedCharacter m τ hτ w
local notation "ρ" => bruhatSchwartzTranslationAction (G := G)

local instance : UniformSpace S := bruhatSchwartzUniformSpace
local instance : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
local instance : T2Space S := bruhatSchwartz_t2
local instance : ContinuousSMul ℂ S := (PolynormableSpace.withSeminorms ℂ S).continuousSMul

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem extendedCharacter_value (g : G) :
    χ g = w ⟨g / τ (m g), by
      change m (g / τ (m g)) = 1
      rw [map_div, hτ, div_self']⟩ := rfl

private theorem extendedCharacter_section (t : Multiplicative ℝ) : χ (τ t) = 1 := by
  rw [extendedCharacter_value]
  have h : (⟨τ t / τ (m (τ t)), by
    change m (τ t / τ (m (τ t))) = 1
    simp only [hτ, div_self', map_one]⟩ : K) = 1 := by
    apply Subtype.ext
    change τ t / τ (m (τ t)) = 1
    rw [hτ, div_self']
  rw [h, map_one]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem extendedCharacter_kernel (k : K) : χ k.val = w k :=
  congrArg (fun a : CircleCharacter K ↦ a k) (extendModulatedCharacter_restrict m τ hτ w)

/-- D.2.2.3(1), in the fixed-space presentation. With left translation
by the inverse argument, the radial profile is multiplied by the inverse
of the extended character. Restriction to the section is the inverse map. -/
theorem exists_bruhatSchwartz_radialIsotype (hm : IsProperMap m) :
    ∃ e : 𝓢(ℝ, ℂ) ≃L[ℂ] fixedSubmodule (compactIsotypicAction K w ρ),
      (∀ f g, (e f : S).val g = f (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ)) ∧
      ∀ u x, e.symm u x = (u : S).val (τ (Multiplicative.ofAdd x)) := by
  obtain ⟨L, hL⟩ := exists_bruhatSchwartz_radialCharacter m
    hm (fun t ↦ ⟨τ t, hτ t⟩) χ⁻¹
  let A := compactIsotypicAction K w ρ
  have hmem (f : 𝓢(ℝ, ℂ)) : L f ∈ fixedSubmodule A := by
    apply (mem_circleIsotype_iff w.toMonoidHom ((ρ).comp (K).subtype) (L f)).mpr
    intro k
    apply Subtype.ext
    funext g
    change (bruhatSchwartz_translate (k : G) (L f)).val g = (w k : ℂ) * (L f).val g
    rw [bruhatSchwartz_translate_apply, hL, hL, map_mul, map_inv, show m k.val = 1 from k.property,
      inv_one, one_mul]
    change f (m g).toAdd * (((χ (k.val⁻¹ * g))⁻¹ : Circle) : ℂ) =
      (w k : ℂ) * (f (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ))
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, extendedCharacter_kernel m τ hτ w k, Circle.coe_mul]
    ring
  let J : 𝓢(ℝ, ℂ) →L[ℂ] fixedSubmodule A := L.codRestrict _ hmem
  let R := (bruhatSchwartz_radialRestriction τ hτ).comp (fixedSubmodule A).subtypeL
  have hRJ (f : 𝓢(ℝ, ℂ)) : R (J f) = f := by
    apply SchwartzMap.ext
    intro x
    change bruhatSchwartz_radialRestriction τ hτ (L f) x = f x
    rw [bruhatSchwartz_radialRestriction_apply, hL, hτ]
    change f x * (((χ (τ (Multiplicative.ofAdd x)))⁻¹ : Circle) : ℂ) = f x
    rw [extendedCharacter_section m τ hτ w, inv_one, Circle.coe_one, mul_one]
  have hJR (u : fixedSubmodule A) : J (R u) = u := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (L (bruhatSchwartz_radialRestriction τ hτ u.val)).val g = u.val.val g
    rw [hL, bruhatSchwartz_radialRestriction_apply]
    let k : K := ⟨g / τ (m g), by
      change m (g / τ (m g)) = 1
      rw [map_div, hτ, div_self']⟩
    have hu := (mem_circleIsotype_iff w.toMonoidHom ((ρ).comp (K).subtype) (u : S)).mp u.property k
    have hx := congrArg (fun w : S ↦ w.val g) hu
    change (bruhatSchwartz_translate k.val u.val).val g = (w k : ℂ) * u.val.val g at hx
    have hg : k.val⁻¹ * g = τ (m g) := by
      change (g / τ (m g))⁻¹ * g = τ (m g)
      rw [inv_div, div_mul_cancel]
    rw [bruhatSchwartz_translate_apply, hg] at hx
    change u.val.val (τ (m g)) * (((χ g)⁻¹ : Circle) : ℂ) = u.val.val g
    have he : χ g = w k := extendedCharacter_value m τ hτ w g
    rw [hx, he, mul_comm (w k : ℂ), mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, mul_one]
  let e : 𝓢(ℝ, ℂ) ≃L[ℂ] fixedSubmodule A :=
    { toLinearEquiv := LinearEquiv.ofLinear J.toLinearMap R.toLinearMap
        (LinearMap.ext hJR) (LinearMap.ext hRJ)
      continuous_toFun := J.continuous
      continuous_invFun := R.continuous }
  exact ⟨e, hL, fun u x ↦ bruhatSchwartz_radialRestriction_apply τ hτ u.val x⟩


/-- The printed multiplier fails at a kernel point whenever the character
differs from its inverse and the radial profile is nonzero at the origin. -/
theorem printed_radialCharacter_not_isotypic
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 ≠ 0) (k : K) (hk : (w k)⁻¹ ≠ w k)
    (u : S) (hu : ∀ g, u.val g = f (m g).toAdd * (χ g : ℂ)) :
    u ∉ fixedSubmodule (compactIsotypicAction K w ρ) := by
  intro h
  have h' := (mem_circleIsotype_iff w.toMonoidHom ((ρ).comp (K).subtype) u).mp h k
  have he := congrArg (fun w : S ↦ w.val 1) h'
  change (bruhatSchwartz_translate (k : G) u).val 1 = (w k : ℂ) * u.val 1 at he
  have hmod : m (k.val⁻¹ : G) = 1 := by rw [map_inv, show m k.val = 1 from k.property, inv_one]
  have hchar : χ (k.val⁻¹ : G) = (w k)⁻¹ := by
    rw [map_inv (χ), extendedCharacter_kernel m τ hτ w k]
  rw [bruhatSchwartz_translate_apply, mul_one, hu, hu, hmod, hchar,
    map_one m, map_one (χ), Circle.coe_one, mul_one] at he
  apply hk
  apply Subtype.ext
  apply mul_left_cancel₀ hf
  exact he.trans (mul_comm _ _)

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]
  [IsProbabilityMeasure ν]

/-- D.2.2.3(1). The same radial isotype equivalence with the manuscript's
Hausdorff coinvariant quotient as target. -/
theorem exists_bruhatSchwartz_radialCoinvariants (hm : IsProperMap m) :
    ∃ P : S →L[ℂ] S, ∃ hP : ∀ f, HasPositivePettisIntegral ν
        (fun k ↦ compactIsotypicAction K w ρ k f) (P f),
      ∃ e : 𝓢(ℝ, ℂ) ≃L[ℂ] (S ⧸ P.ker), ∀ f g,
        ((compactAverage_quotientEquiv ν (compactIsotypicAction K w ρ) P hP (e f) :
          S)).val g = f (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : T2Space S := bruhatSchwartz_t2
  obtain ⟨P, hP₀⟩ := exists_bruhatSchwartz_compactAverage K ν w
  have hP : ∀ f, HasPositivePettisIntegral ν (fun k ↦ compactIsotypicAction K w ρ k f) (P f) := hP₀
  obtain ⟨e, he, _⟩ := exists_bruhatSchwartz_radialIsotype m τ hτ w hm
  let Q := compactAverage_quotientEquiv ν (compactIsotypicAction K w ρ) P hP
  exact ⟨P, hP, e.trans Q.symm, fun f g ↦ by
    change (Q (Q.symm (e f)) : S).val g = _
    rw [Q.apply_symm_apply]
    exact he f g⟩


section Ambient

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [T2Space E] [PolynormableSpace ℂ E] [CompleteSpace E]
  [ContinuousSMul ℂ E]

/-- D.2.2.3(2), with dense range. The original radial subspace carries the
topology induced by the ambient injection. Multiplication by the inverse
character identifies its completion with the ambient isotypic quotient. -/
theorem exists_bruhatSchwartz_radialCompletion (hm : IsProperMap m)
    (B : G →* (E →L[ℂ] E)) (hB : Continuous (fun p : G × E ↦ B p.1 p.2))
    (i : S →L[ℂ] E) (hi : Injective i) (hd : DenseRange i)
    (he : ∀ g f, i (ρ g f) = B g (i f))
    (M : S ≃ₗ[ℂ] S)
    (hM : ∀ f g, (M f).val g = f.val g * (χ g : ℂ))
    (hMind : @IsInducing S S (TopologicalSpace.induced i inferInstance)
      (TopologicalSpace.induced i inferInstance) M) :
    ∃ (L₀ : 𝓢(ℝ, ℂ) →L[ℂ] S) (P : E →L[ℂ] E),
      (∀ f g, (L₀ f).val g = f (m g).toAdd) ∧
      (∀ u, HasPositivePettisIntegral ((ν univ)⁻¹ • ν)
        (fun k ↦ compactIsotypicAction K w B k u) (P u)) ∧
      ∃ J : 𝓢(ℝ, ℂ) →L[ℂ] (E ⧸ P.ker),
        (∀ f, J f = P.ker.mkQ (i (M.symm (L₀ f)))) ∧ DenseRange J ∧
        @IsEmbedding 𝓢(ℝ, ℂ) (E ⧸ P.ker)
          (TopologicalSpace.induced (i ∘ L₀) inferInstance) inferInstance J ∧
        @CompleteSpace (E ⧸ P.ker) (IsTopologicalAddGroup.rightUniformSpace _) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : T2Space S := bruhatSchwartz_t2
  obtain ⟨L₀, h₀⟩ := exists_bruhatSchwartz_radialCharacter m hm (fun t ↦ ⟨τ t, hτ t⟩) 1
  have hL₀ (f : 𝓢(ℝ, ℂ)) (g : G) : (L₀ f).val g = f (m g).toAdd := by
    simpa using h₀ f g
  obtain ⟨e, hE, _⟩ := exists_bruhatSchwartz_radialIsotype m τ hτ w hm
  have hL (f : 𝓢(ℝ, ℂ)) : M (e f : S) = L₀ f := by
    apply Subtype.ext
    funext g
    rw [hM, hE, hL₀, mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, mul_one]
  obtain ⟨R, P, hR, hP, _, _, _, _, j, l, hj, hl, hjapp, hlapp, hDense⟩ :=
    bruhatIsotypeComparison K ν w B hB i hi he
  let B₀ := compactIsotypicAction K w B
  let μ := (ν univ)⁻¹ • ν
  letI : IsProbabilityMeasure μ := inferInstance
  letI : μ.IsHaarMeasure := Measure.IsHaarMeasure.smul ν
    (ENNReal.inv_ne_zero.mpr (measure_ne_top ν univ)) (ENNReal.inv_ne_top.mpr (NeZero.ne (ν univ)))
  let Q := compactAverage_quotientEquiv μ B₀ P hP
  let J₀ : 𝓢(ℝ, ℂ) →L[ℂ] fixedSubmodule B₀ := l.comp e.toContinuousLinearMap
  let J : 𝓢(ℝ, ℂ) →L[ℂ] (E ⧸ P.ker) := Q.symm.toContinuousLinearMap.comp J₀
  have hJ (f : 𝓢(ℝ, ℂ)) : J f = P.ker.mkQ (i (M.symm (L₀ f))) := by
    change P.ker.mkQ ((l (e f) : E)) = _
    rw [hlapp, ← hL, M.symm_apply_apply]
  have hDense₀ : DenseRange J₀ := (hDense hd).2.comp e.surjective.denseRange l.continuous
  have hEmb₀ : @IsEmbedding 𝓢(ℝ, ℂ) (fixedSubmodule B₀)
      (TopologicalSpace.induced (i ∘ L₀) inferInstance) inferInstance J₀ := by
    refine @IsEmbedding.mk 𝓢(ℝ, ℂ) (fixedSubmodule B₀)
      (TopologicalSpace.induced (i ∘ L₀) inferInstance) inferInstance
      (fun f ↦ J₀ f) ?_ (hl.comp e.injective)
    refine @IsInducing.mk 𝓢(ℝ, ℂ) (fixedSubmodule B₀)
      (TopologicalSpace.induced (i ∘ L₀) inferInstance) inferInstance (fun f ↦ J₀ f) ?_
    let V : 𝓢(ℝ, ℂ) → S := fun f ↦ e f
    have hradial : (i ∘ L₀ : 𝓢(ℝ, ℂ) → E) = (i ∘ M) ∘ V :=
      funext fun f ↦ congrArg i (hL f).symm
    have hj₀ : ((↑) : fixedSubmodule B₀ → E) ∘ J₀ = i ∘ V :=
      funext fun f ↦ hlapp (e f)
    change TopologicalSpace.induced (i ∘ L₀) _ =
      TopologicalSpace.induced J₀ (TopologicalSpace.induced ((↑) : fixedSubmodule B₀ → E) _)
    have hMtop : TopologicalSpace.induced i inferInstance =
        TopologicalSpace.induced M (TopologicalSpace.induced i inferInstance) :=
      @IsInducing.eq_induced S S (TopologicalSpace.induced i inferInstance)
        (TopologicalSpace.induced i inferInstance) (fun f ↦ M f) hMind
    rw [hradial, ← induced_compose, ← induced_compose, ← hMtop, induced_compose,
      induced_compose, hj₀]
  refine ⟨L₀, P, hL₀, hP, J, hJ,
    Q.symm.surjective.denseRange.comp hDense₀ Q.symm.continuous,
    ?_, ?_⟩
  · exact @IsEmbedding.comp 𝓢(ℝ, ℂ) (fixedSubmodule B₀) (E ⧸ P.ker)
      (fun f ↦ J₀ f) (fun u ↦ Q.symm u)
      (TopologicalSpace.induced (i ∘ L₀) inferInstance) inferInstance inferInstance
      Q.symm.toHomeomorph.isEmbedding hEmb₀
  letI : IsUniformAddGroup (fixedSubmodule B₀) := (fixedSubmodule B₀).toAddSubgroup.isUniformAddGroup
  letI : IsClosed (fixedSubmodule B₀ : Set E) := fixedSubmodule_isClosed B₀
  letI : CompleteSpace (fixedSubmodule B₀) := inferInstance
  letI : UniformSpace (E ⧸ P.ker) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E ⧸ P.ker) := isUniformAddGroup_of_addCommGroup
  exact (AddMonoidHom.isUniformInducing_of_isInducing (f := Q.toLinearEquiv.toAddMonoidHom)
    Q.toHomeomorph.isInducing).completeSpace_congr Q.surjective |>.mpr inferInstance

end Ambient

/-- Adjoining a trivial scalar summand gives the clause (2) obstruction at
the trivial character. All lifted radial profiles have zero scalar coordinate,
whereas the ambient fixed space contains the scalar summand. -/
theorem radialCompletion_scalarSummand_not_dense
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (V : Submodule ℂ (X × ℂ)) (hOne : ((0, 1) : X × ℂ) ∈ V)
    (L : Y → V) (hL : ∀ y, (L y : X × ℂ).2 = 0) : ¬ DenseRange L := by
  intro hd
  have h : IsClosed {v : V | (v.val : X × ℂ).2 = 0} :=
    isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have he : (⟨(0, 1), hOne⟩ : V) ∈ {v : V | (v.val : X × ℂ).2 = 0} :=
    hd.induction_on (p := fun v : V ↦ (v.val : X × ℂ).2 = 0) ⟨(0, 1), hOne⟩ h hL
  exact one_ne_zero (show (1 : ℂ) = 0 from he)

end Isotype

end

end Masullo
