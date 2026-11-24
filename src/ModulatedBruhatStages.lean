import BruhatSchwartz
import ElementaryRadialSchwartz
import ModulationSection
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

open Filter Function Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

private theorem monoidHom_eq_one_of_mem_compact_subgroup (m : G →ₜ* Multiplicative ℝ)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (k : K) : m k.val = 1 := by
  let l (x : G) : ℝ := (m x).toAdd
  have hl : Continuous l := continuous_toAdd.comp m.continuous
  obtain ⟨B, hB⟩ := ((hK.image hl).image continuous_abs).bddAbove
  by_contra h
  have ht : 0 < |l k.val| := abs_pos.mpr (show l k.val ≠ 0 from h)
  obtain ⟨n, hn⟩ := exists_nat_gt (B / |l k.val|)
  have hh : |l (k.val ^ n)| ≤ B := hB ⟨l (k.val ^ n),
    ⟨k.val ^ n, K.pow_mem k.property n, rfl⟩, rfl⟩
  have hlog : l (k.val ^ n) = (n : ℝ) * l k.val := by
    change (m (k.val ^ n)).toAdd = _
    rw [map_pow]
    change n • l k.val = _
    rw [nsmul_eq_mul]
  rw [hlog, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hh
  exact (not_lt_of_ge hh) ((div_lt_iff₀ ht).mp hn)

namespace LCAStructuralPair

/-- Proper real modulations vanish on the compact kernels of all Bruhat stages. -/
theorem modulation_eq_one_on_kernel (P : LCAStructuralPair G) (m : G →ₜ* Multiplicative ℝ)
    (k : P.kernel) : m k.val = 1 := by
  have hcomp : IsCompact (P.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  exact monoidHom_eq_one_of_mem_compact_subgroup m P.kernel hcomp k

/-- Descend a continuous homomorphism through a Bruhat stage when it is
trivial on the stage kernel. -/
def descendHom {H : Type*} [Group H] [TopologicalSpace H] (P : LCAStructuralPair G)
    (f : G →ₜ* H) (hf : ∀ k : P.kernel, f k.val = 1) : P.StageQuotient →ₜ* H :=
  ⟨QuotientGroup.lift _ (f.toMonoidHom.comp P.upper.val.subtype) (fun x hx => hf ⟨x.val, hx⟩),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (f.continuous.comp continuous_subtype_val)⟩

@[simp] theorem descendHom_mk {H : Type*} [Group H] [TopologicalSpace H] (P : LCAStructuralPair G)
    (f : G →ₜ* H) (hf : ∀ k : P.kernel, f k.val = 1) (x : P.upper.val) :
    P.descendHom f hf (QuotientGroup.mk x) = f x.val := rfl

/-- The logarithmic coordinate on any elementary stage is proper. -/
theorem descendModulation_isProperMap (P : LCAStructuralPair G) (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) : IsProperMap (P.descendHom m (P.modulation_eq_one_on_kernel m)) := by
  let l := P.descendHom m (P.modulation_eq_one_on_kernel m)
  refine isProperMap_iff_isCompact_preimage.mpr ⟨l.continuous, fun C hC => ?_⟩
  have hp : IsProperMap (fun x : P.upper.val => m x.val) :=
    hm.comp (P.upper.val.isClosed_of_isOpen P.upper.property.1).isProperMap_subtypeVal
  have he : l ⁻¹' C = (QuotientGroup.mk : P.upper.val → P.StageQuotient) ''
      ((fun x : P.upper.val => m x.val) ⁻¹' C) := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · exact fun h => ⟨y, h, rfl⟩
    · rintro ⟨z, hz, heq⟩
      rw [← heq]
      exact hz
  rw [he]
  exact (hp.isCompact_preimage hC).image QuotientGroup.continuous_mk

end LCAStructuralPair

/-- With surjective proper real modulation the whole group can serve as
the open compactly generated upper subgroup of a Bruhat stage. -/
theorem exists_modulatedBruhat_upper_eq_top (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m) :
    ∃ J : OpenCompactlyGeneratedSubgroups G, J.val = ⊤ := by
  obtain ⟨τ, hτ⟩ := exists_realModulation_section m hm hms
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains
    (hm.isCompact_preimage (K := {1}) isCompact_singleton)
  let f (x : ℝ) := τ (Multiplicative.ofAdd x)
  have hf : Continuous f := τ.continuous.comp continuous_ofAdd
  have hpre : IsClopen (f ⁻¹' (J.val : Set G)) :=
    ⟨(J.val.isClosed_of_isOpen J.property.1).preimage hf, J.property.1.preimage hf⟩
  have hτJ : ∀ x, τ x ∈ J.val := by
    have he := hpre.eq_univ ⟨0, by change τ 1 ∈ J.val; rw [map_one]; exact J.val.one_mem⟩
    intro x
    change x.toAdd ∈ f ⁻¹' (J.val : Set G)
    rw [he]
    exact mem_univ _
  refine ⟨J, top_unique ?_⟩
  intro x _
  have hx : x / τ (m x) ∈ m ⁻¹' ({1} : Set (Multiplicative ℝ)) := by
    change m (x / τ (m x)) = 1
    rw [map_div, hτ, div_self']
  simpa only [div_mul_cancel] using J.val.mul_mem (hJ hx) (hτJ (m x))

/-- Any continuous character and the proper modulation simultaneously
descend through a single whole-group Bruhat stage. -/
theorem exists_modulatedBruhat_character_stage (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m) (χ : PontryaginDual G) :
    ∃ P : LCAStructuralPair G, P.upper.val = ⊤ ∧ ∀ k : P.kernel, χ k.val = 1 := by
  obtain ⟨J, hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  obtain ⟨H, hχ⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 χ
  let P := LCAStructuralPair.ofDual J H (show lcaDualAnnihilator H.val ≤ J.val from hJ ▸ le_top)
  exact ⟨P, hJ, fun k => (mem_lcaDualAnnihilator_iff H.val k.val).mp k.property ⟨χ, hχ⟩⟩

/-- Logarithmic Schwartz profiles times continuous unitary characters are
actual Schwartz–Bruhat functions on a positive-real modulated group. -/
theorem modulatedBruhat_radialCharacter_mem (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m) (χ : PontryaginDual G) (f : 𝓢(ℝ, ℂ)) :
    (fun g => f (m g).toAdd * (χ g : ℂ)) ∈ bruhatSchwartzSubmodule (G := G) := by
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
  let q : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor :=
    ⟨_, elementarySchwartz_radialCharacter_mem l hl ψ f⟩
  refine ⟨⟨P, p⟩, q, funext fun g => ?_⟩
  have hg : g ∈ P.upper.val := hP.symm ▸ Subgroup.mem_top g
  let x : P.upper.val := ⟨g, hg⟩
  change P.realizeSchwartz p q x.val = _
  rw [P.realizeSchwartz_apply_of_mem]
  change f ((P.descendHom m (P.modulation_eq_one_on_kernel m))
    (p.equiv.symm (p.equiv (QuotientGroup.mk x)))).toAdd *
    ((P.descendHom (show CircleCharacter G from χ) hχ)
    (p.equiv.symm (p.equiv (QuotientGroup.mk x))) : ℂ) = _
  rw [p.equiv.symm_apply_apply, P.descendHom_mk]
  rfl

end

end Masullo
