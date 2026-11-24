import BruhatSupportedWindow
import BruhatCyclicPeriodizationCorollary
import CyclicQuotientBasisTransport

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 1800000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (γ : G)

local notation "Q" => G ⧸ Subgroup.zpowers γ
local notation "E" => ModulatedExponentialInductive m univ

variable [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

/-- Invariance under the image of K in the cyclic quotient. -/
def bruhatCyclicQuotientInvariant (K : Subgroup G) : Submodule ℂ (BruhatSchwartz Q) where
  carrier := {g | ∀ (k : K) x, g.val (QuotientGroup.mk (k.val⁻¹) * x) = g.val x}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' {f g} hf hg k x := by
    change f.val _ + g.val _ = f.val x + g.val x
    rw [hf, hg]
  smul_mem' c f hf k x := by
    change c • f.val _ = c • f.val x
    rw [hf k x]

/-- Cyclic periodization and its supported cutoff section both preserve
invariance under a subgroup of the norm-one kernel. -/
theorem exists_supportedInvariant_periodization_section
    (hm : IsProperMap m) (hms : Surjective m) (hγ : 0 < (m γ).toAdd)
    (K : Subgroup G) (hK : K ≤ m.toMonoidHom.ker)
    (a b : ℝ) (hab : a + (m γ).toAdd < b) :
    let U := bruhatSupportedInvariant m K ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
    let V := bruhatCyclicQuotientInvariant γ K
    let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
    let B := bruhatCyclicPeriodization m hm γ hγ hms
    ∃ (T : U →L[ℂ] V) (S : V →L[ℂ] U),
      RightInverse S T ∧ ∀ f : U, (T f).val = B (J f.val) := by
  dsimp only
  let U := bruhatSupportedInvariant m K ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
  let V := bruhatCyclicQuotientInvariant γ K
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let B := bruhatCyclicPeriodization m hm γ hγ hms
  have hB := bruhatCyclicPeriodization_apply m hm γ hγ hms
  let T₀ : U →L[ℂ] BruhatSchwartz Q := B.comp (J.comp U.subtypeL)
  have hT (u : U) : T₀ u ∈ V := by
    intro k q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change (B (J u.val)).val (QuotientGroup.mk k.val⁻¹ * QuotientGroup.mk x) =
      (B (J u.val)).val (QuotientGroup.mk x)
    rw [← QuotientGroup.mk_mul, hB, hB,
      bruhatSchwartz_cyclicOrbitSum_apply, bruhatSchwartz_cyclicOrbitSum_apply]
    refine tsum_congr fun n ↦ ?_
    change u.val.val (γ ^ n * (k.val⁻¹ * x)) = u.val.val (γ ^ n * x)
    rw [mul_left_comm]
    exact u.property.2 k _
  obtain ⟨c, hc, hs, hright⟩ := exists_weightedCyclicPeriodization_cutoffSection_on_window
    m hm hms γ hγ B hB a b hab univ (mem_univ 0)
  let R := bruhatCyclicDecayCutoffLift m hm hms γ hγ univ c hc (Icc a b) isCompact_Icc hs
  have hval (v : BruhatSchwartz Q) (x : G) : (R v).val x = c (m x).toAdd * v.val (QuotientGroup.mk x) :=
    bruhatCyclicCutoffLift_apply m hm hms γ hγ c hc (Icc a b) isCompact_Icc hs v x
  have hR (v : V) : R v.val ∈ U := by
    constructor
    · intro x hx
      by_contra h
      have hz := notMem_support.mp fun hm ↦ h (hs hm)
      exact hx ((hval v.val x).trans (by rw [hz, zero_mul]))
    · intro k x
      have hk : m k.val = 1 := hK k.property
      have he : (m (k.val⁻¹ * x)).toAdd = (m x).toAdd := by rw [map_mul, map_inv, hk, inv_one, one_mul]
      rw [hval, hval, he, QuotientGroup.mk_mul]
      exact congrArg (c (m x).toAdd * ·) (v.property k (QuotientGroup.mk x))
  let T := T₀.codRestrict V hT
  let S := (R.comp V.subtypeL).codRestrict U hR
  refine ⟨T, S, fun v ↦ ?_, fun _ ↦ rfl⟩
  apply Subtype.ext
  exact hright v.val

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)] in
/-- Every cyclic coset has a representative in a logarithmic window wider
than the period. -/
theorem bruhatCyclicQuotient_image_window (hγ : 0 < (m γ).toAdd)
    (a b : ℝ) (hab : a + (m γ).toAdd < b) :
    (QuotientGroup.mk : G → Q) '' ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨n, hn⟩ := openInterval_covers_integerTranslations hγ hab (m x).toAdd
  refine ⟨γ ^ n * x, ?_, ?_⟩
  · change (m (γ ^ n * x)).toAdd ∈ Icc a b
    have hlog : (m (γ ^ n * x)).toAdd = (m x).toAdd + (m γ).toAdd * (n : ℝ) := by
      simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul]
      ring
    rw [hlog]
    exact Ioo_subset_Icc_self hn
  · rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 (Subgroup.zpow_mem_zpowers γ n), one_mul]

/-- The supported quotient carries the topology of the invariant tests
on the cyclic quotient, with periodization as its canonical map. -/
theorem exists_supportedInvariant_periodization_quotientEquiv
    (hm : IsProperMap m) (hms : Surjective m) (hγ : 0 < (m γ).toAdd)
    (K : Subgroup G) (hK : K ≤ m.toMonoidHom.ker)
    (a b : ℝ) (hab : a + (m γ).toAdd < b) :
    let U := bruhatSupportedInvariant m K ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
    let V := bruhatCyclicQuotientInvariant γ K
    let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
    let B := bruhatCyclicPeriodization m hm γ hγ hms
    ∃ (T : U →L[ℂ] V) (e : (U ⧸ T.ker) ≃L[ℂ] V),
      ∀ f : U, (e (T.ker.mkQ f)).val = B (J f.val) := by
  dsimp only
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : ContinuousSMul ℂ (BruhatSchwartz Q) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz Q)).continuousSMul
  let U := bruhatSupportedInvariant m K ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
  let V := bruhatCyclicQuotientInvariant γ K
  obtain ⟨T, S, hS, hT⟩ := exists_supportedInvariant_periodization_section m γ hm hms hγ
    K hK a b hab
  obtain ⟨e, he⟩ := splitQuotientEquiv_scaled (X := ↥U) (Y := ↥V) T S hS 1 one_ne_zero
  refine ⟨T, e, fun f ↦ ?_⟩
  rw [he, one_smul]
  exact hT f

end

end Masullo
