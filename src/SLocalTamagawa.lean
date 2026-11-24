import AdelicExtension
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Constructions.Pi

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- In mixed embedding coordinates the manuscript's Archimedean product
uses one Lebesgue factor on each real place and twice Lebesgue measure on
each complex place. -/
def archAdditiveTamagawa : Measure (mixedEmbedding.mixedSpace F) :=
  ((2 : ℝ≥0) ^ InfinitePlace.nrComplexPlaces F) • volume

theorem archAdditiveTamagawa_domain :
    archAdditiveTamagawa F (signedMixedDomain F) = (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) := by
  rw [archAdditiveTamagawa, Measure.smul_apply]
  change (↑((2 : ℝ≥0) ^ InfinitePlace.nrComplexPlaces F) : ℝ≥0∞) *
    volume (signedMixedDomain F) = _
  rw [signedMixedDomain, mixedEmbedding.volume_fundamentalDomain_latticeBasis]
  simp only [ENNReal.coe_pow, ENNReal.coe_ofNat]
  rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
    one_pow, one_mul]

theorem archAdditiveTamagawa_domain_ne_one (h : 1 < Module.finrank ℚ F) :
    archAdditiveTamagawa F (signedMixedDomain F) ≠ 1 := by
  rw [archAdditiveTamagawa_domain]
  have hh := NumberField.abs_discr_gt_two h
  have hn : (1 : ℝ≥0) < ‖discr F‖₊ := by
    exact_mod_cast (show (1 : ℝ) < ‖discr F‖ by
      rw [Int.norm_eq_abs]
      exact_mod_cast ((show (1 : ℤ) < 2 by decide).trans hh))
  exact ne_of_gt (by exact_mod_cast (show (1 : ℝ≥0) < NNReal.sqrt ‖discr F‖₊ by
    simpa using NNReal.sqrt_lt_sqrt.mpr hn))

private abbrev ArchClass :=
  mixedEmbedding.mixedSpace F ⧸ (mixedEmbedding.integerLattice F).toAddSubgroup

local instance : MeasurableSpace (ArchClass F) := borel _
local instance : BorelSpace (ArchClass F) := ⟨rfl⟩

/-- The Archimedean quotient measure induced by counting the lattice
is the pushforward of Haar restricted to its signed domain. -/
def archTamagawaClassMeasure : Measure (ArchClass F) :=
  Measure.map QuotientAddGroup.mk ((archAdditiveTamagawa F).restrict (signedMixedDomain F))

theorem archTamagawaClassMeasure_mass :
    archTamagawaClassMeasure F univ = (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) := by
  have hm : Measurable (QuotientAddGroup.mk : mixedEmbedding.mixedSpace F → ArchClass F) :=
    QuotientAddGroup.continuous_mk.measurable
  rw [archTamagawaClassMeasure, Measure.map_apply hm MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    archAdditiveTamagawa_domain]

/-- For S consisting only of the infinite places, the printed product
of local factors gives quotient volume different from one. -/
theorem printed_sLocalTamagawa_normalization_fails (h : 1 < Module.finrank ℚ F) :
    archTamagawaClassMeasure F univ ≠ 1 := by
  rw [archTamagawaClassMeasure_mass, ← archAdditiveTamagawa_domain F]
  exact archAdditiveTamagawa_domain_ne_one F h

section FinitePlaces

private abbrev Place := HeightOneSpectrum (𝓞 F)

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)]

/-- The product of the prescribed Archimedean measure and the selected
finite local measures, before normalizing the additive quotient. -/
def sLocalAdditiveProduct (S : Finset (Place F))
    (m : (v : S) → Measure (v.val.adicCompletion F)) : Measure (SAdeles F S) :=
  (Measure.map (infiniteAdeleMixedHomeomorph F).symm (archAdditiveTamagawa F)).prod (Measure.pi m)

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)] in
theorem sLocalAdditiveProduct_domain (S : Finset (Place F))
    (m : (v : S) → Measure (v.val.adicCompletion F)) [∀ v, SigmaFinite (m v)] :
    sLocalAdditiveProduct F S m (signedSAdelicDomain F S) =
      (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) *
        ∏ v : S, m v (v.val.adicCompletionIntegers F) := by
  let e := infiniteAdeleMixedHomeomorph F
  let A := e ⁻¹' signedMixedDomain F
  let I := Set.pi univ (fun v : S => (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)))
  have hA : MeasurableSet A :=
    (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)).preimage e.continuous.measurable
  have he : e.symm ⁻¹' A = signedMixedDomain F := by
    ext x
    change e (e.symm x) ∈ signedMixedDomain F ↔ _
    rw [e.apply_symm_apply]
  have hs : signedSAdelicDomain F S = A ×ˢ I :=
    Set.ext fun _ => and_congr_right fun _ => Set.mem_univ_pi.symm
  rw [sLocalAdditiveProduct, hs, Measure.prod_prod, Measure.map_apply e.symm.continuous.measurable hA,
    he, archAdditiveTamagawa_domain, Measure.pi_pi]

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)] in
/-- The normalized S-local measure is obtained by dividing by the signed
domain's product volume. -/
theorem sLocalAdditiveProduct_normalized_domain (S : Finset (Place F))
    (m : (v : S) → Measure (v.val.adicCompletion F)) [∀ v, SigmaFinite (m v)]
    (hc₀ : (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) * ∏ v : S, m v (v.val.adicCompletionIntegers F) ≠ 0)
    (hcTop : (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) * ∏ v : S, m v (v.val.adicCompletionIntegers F) ≠ ∞) :
    (((NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) *
      ∏ v : S, m v (v.val.adicCompletionIntegers F))⁻¹ • sLocalAdditiveProduct F S m)
        (signedSAdelicDomain F S) = 1 := by
  rw [Measure.smul_apply, smul_eq_mul, sLocalAdditiveProduct_domain,
    ENNReal.inv_mul_cancel hc₀ hcTop]

end FinitePlaces

end

end Masullo
