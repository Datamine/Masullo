import ModulatedRadialIsotypes
import ModulatedDecayIsotypes
import ExponentialDecayStructure

open Filter Function Set Topology
open scoped SchwartzMap

noncomputable section

namespace Masullo

set_option maxHeartbeats 1900000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G)
  (hτ : ∀ t, m (τ t) = t) (w : PontryaginDual m.toMonoidHom.ker)

variable (I : Set ℝ) (hI : I.Nonempty)

local notation "X" => PositiveRealExponentialDecay I
local notation "E" => ModulatedExponentialInductive m I
local notation "K" => m.toMonoidHom.ker
local notation "H" => modulatedDecayIsotype m w I
local notation "χ" => extendModulatedCharacter m τ hτ w

/-- The restriction to the modulus section is continuous for the weighted
Schwartz topology, including on the full inductive-limit space. -/
def modulatedDecayRadialRestriction : E →L[ℂ] X := by
  let R := bruhatSchwartz_radialRestriction τ hτ
  let L : E →ₗ[ℂ] (ℝ → ℂ) :=
    { toFun := fun f x ↦ f.val (τ (Multiplicative.ofAdd x))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have h (f : E) (a : I) (x : ℝ) :
      R (modulatedDecayTwistCLM m I a f) x = logExponentialWeight a (L f) x := by
    rw [bruhatSchwartz_radialRestriction_apply]
    change modulatedExponentialWeight m a f.val (τ (Multiplicative.ofAdd x)) = _
    rw [modulatedExponentialWeight_apply, hτ]
    exact Complex.real_smul
  let T : E →ₗ[ℂ] X := L.codRestrict _ (fun f ↦
    (Submodule.mem_iInf _).mpr fun a ↦ ⟨R (modulatedDecayTwistCLM m I a f), funext (h f a)⟩)
  refine ⟨T, (positiveRealExponentialDecay_isEmbedding I hI).isInducing.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro a
  refine (R.continuous.comp (modulatedDecayTwistCLM m I a).continuous).congr fun f ↦
    SchwartzMap.ext fun x ↦ ?_
  erw [h f a x, logExponentialDecayTwist_apply]
  rfl

@[simp] theorem modulatedDecayRadialRestriction_apply (f : E) (x : ℝ) :
    (modulatedDecayRadialRestriction m τ hτ I hI f).val x =
      f.val (τ (Multiplicative.ofAdd x)) := rfl

include hI in
set_option maxHeartbeats 4400000 in
private theorem exists_modulatedDecayRadialMap (hm : IsProperMap m) :
    ∃ J : X →L[ℂ] E, ∀ f g, (J f).val g =
      f.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ) := by
  obtain ⟨P, A, hA⟩ := exists_wholeBruhatStage_radialCharacter m hm (fun t ↦ ⟨τ t, hτ t⟩) χ⁻¹
  let L : X →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f g ↦ f.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ)
      map_add' _ _ := funext fun _ ↦ add_mul _ _ _
      map_smul' _ _ := funext fun _ ↦ mul_assoc _ _ _ }
  have hP (a : I) (f : X) :
      P.val.realize (A (logExponentialDecayTwist I a f)) =
        modulatedExponentialWeight m a (L f) := by
    funext g
    rw [hA]
    erw [logExponentialDecayTwist_apply, modulatedExponentialWeight_apply]
    rw [Complex.real_smul]
    exact mul_assoc _ _ _
  let T : X →ₗ[ℂ] WholeBruhatDecayStage m I P :=
    (WholeBruhatDecayStage.algebraicEquiv (p := P)).symm.toLinearMap.comp
      (L.codRestrict _ (fun f ↦ (Submodule.mem_iInf _).mpr fun a ↦ ⟨_, hP a f⟩))
  have hT : Continuous T := (WholeBruhatDecayStage.continuous_iff T).mpr fun a ↦ by
    have h := (continuous_apply a).comp
      (positiveRealExponentialDecay_isEmbedding I hI).continuous
    refine (A.continuous.comp h).congr fun f ↦ ?_
    apply P.val.1.realizeSchwartz_injective P.val.2
    change P.val.realize (A (logExponentialDecayTwist I a f)) =
      P.val.realize (WholeBruhatDecayStage.twist P a (T f))
    exact (hP a f).trans (WholeBruhatDecayStage.realize_twist P a (T f)).symm
  let J : X →L[ℂ] E :=
    ⟨(ModulatedExponentialInductive.stageMap P).comp T,
      (ModulatedExponentialInductive.stageMap_continuous P).comp hT⟩
  have hJ (f : X) (g : G) :
      (J f).val g = f.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ) := rfl
  exact ⟨J, hJ⟩

include hI in
set_option maxHeartbeats 4400000 in
/-- The weighted exponential-decay isotype is the scalar exponential Schwartz
space, with the actual inductive topology on the ambient test space. -/
theorem exists_modulatedDecayRadialIsotype (hm : IsProperMap m) :
    ∃ e : X ≃L[ℂ] H, (∀ f g, (e f : E).val g =
      f.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ)) ∧
      ∀ u x, (e.symm u).val x = (u : E).val (τ (Multiplicative.ofAdd x)) := by
  obtain ⟨J, hJ⟩ := exists_modulatedDecayRadialMap m τ hτ w I hI hm
  have hχk (k : K) : χ k.val = w k :=
    congrArg (fun a : CircleCharacter K ↦ a k) (extendModulatedCharacter_restrict m τ hτ w)
  have hmem (f : X) : J f ∈ H := by
    intro k g
    rw [hJ, hJ, map_mul m, map_inv m, show m k.val = 1 from k.property, inv_one, one_mul,
      map_mul (χ), map_inv (χ), mul_inv_rev, inv_inv, hχk, Circle.coe_mul]
    ring
  let J₀ := J.codRestrict H hmem
  let R := (modulatedDecayRadialRestriction m τ hτ I hI).comp (H).subtypeL
  have hχ (g : G) :
      χ g = w ⟨g / τ (m g), by
        change m (g / τ (m g)) = 1
        rw [map_div, hτ, div_self']⟩ := rfl
  have hRJ (f : X) : R (J₀ f) = f := by
    apply Subtype.ext
    funext x
    change (modulatedDecayRadialRestriction m τ hτ I hI (J f)).val x = f.val x
    rw [modulatedDecayRadialRestriction_apply, hJ, hτ, hχ]
    have ht : ((⟨τ (Multiplicative.ofAdd x) / τ (m (τ (Multiplicative.ofAdd x))), by
        change m (τ (Multiplicative.ofAdd x) / τ (m (τ (Multiplicative.ofAdd x)))) = 1
        simp only [hτ, div_self', map_one]⟩ : K)) = 1 := by
      apply Subtype.ext
      change τ (Multiplicative.ofAdd x) / τ (m (τ (Multiplicative.ofAdd x))) = 1
      rw [hτ, div_self']
    rw [ht, map_one, inv_one, Circle.coe_one, mul_one]
    rfl
  have hJR (u : H) : J₀ (R u) = u := by
    apply Subtype.ext
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext g
    change (J (R u)).val g = u.val.val g
    rw [hJ]
    change (modulatedDecayRadialRestriction m τ hτ I hI u.val).val (m g).toAdd *
      (((χ g)⁻¹ : Circle) : ℂ) = u.val.val g
    rw [modulatedDecayRadialRestriction_apply]
    let k : K := ⟨g / τ (m g), by
      change m (g / τ (m g)) = 1
      rw [map_div, hτ, div_self']⟩
    have hh : u.val.val (k.val⁻¹ * g) = (w k : ℂ) * u.val.val g := u.property k g
    have hg : k.val⁻¹ * g = τ (m g) := by
      change (g / τ (m g))⁻¹ * g = τ (m g)
      rw [inv_div, div_mul_cancel]
    rw [hg] at hh
    change u.val.val (τ (m g)) * (((χ g)⁻¹ : Circle) : ℂ) = _
    rw [hh, show χ g = w k from hχ g, mul_comm (w k : ℂ), mul_assoc,
      ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, mul_one]
  let e : X ≃L[ℂ] H := ⟨LinearEquiv.ofLinear J₀.toLinearMap R.toLinearMap
      (LinearMap.ext hJR) (LinearMap.ext hRJ), J₀.continuous, R.continuous⟩
  exact ⟨e, hJ, fun u x ↦ modulatedDecayRadialRestriction_apply m τ hτ I hI u.val x⟩

private theorem univInterval_nonempty : (Set.univ : Set ℝ).Nonempty := ⟨0, mem_univ _⟩

/-- Restriction to the modulus section for the entire exponential Schwartz space. -/
def modulatedExponentialRadialRestriction :
    ModulatedExponentialInductive m univ →L[ℂ] PositiveRealExponentialDecay univ :=
  modulatedDecayRadialRestriction m τ hτ univ univInterval_nonempty

@[simp] theorem modulatedExponentialRadialRestriction_apply
    (f : ModulatedExponentialInductive m univ) (x : ℝ) :
    (modulatedExponentialRadialRestriction m τ hτ f).val x =
      f.val (τ (Multiplicative.ofAdd x)) := rfl

/-- The entire exponential isotype has the same radial identification. -/
theorem exists_modulatedExponentialRadialIsotype (hm : IsProperMap m) :
    ∃ e : PositiveRealExponentialDecay univ ≃L[ℂ] modulatedDecayIsotype m w univ,
      (∀ f g, (e f : ModulatedExponentialInductive m univ).val g =
        f.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ)) ∧
      ∀ u x, (e.symm u).val x =
        (u : ModulatedExponentialInductive m univ).val (τ (Multiplicative.ofAdd x)) :=
  exists_modulatedDecayRadialIsotype m τ hτ w univ univInterval_nonempty hm

end Masullo
