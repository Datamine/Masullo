import LogDerivativeResidue
import ManuscriptHeckeRegularity

open Complex Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The actual completed Hecke continuation has the zero multiplicity as
its residue weight, with a subtraction at each of the two norm-twist poles. -/
theorem exists_manuscriptCompletedHecke_explicit_residues (χ : PontryaginDual (IdeleClass F))
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ L : ℂ → ℂ, MeromorphicOn L univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      ∀ (Φ : ℂ → ℂ) (p : ℂ), AnalyticAt ℂ Φ p →
        let b := (t : ℂ) * I
        let d := MeromorphicOn.divisor L univ p
        meromorphicResidue (Φ * logDeriv L) p = (↑(max d 0) : ℂ) * Φ p -
          (if heckeNormOneRestriction F χ = 1 ∧ (p = b ∨ p = 1 + b) then Φ p else 0) := by
  obtain ⟨_, _, _, L, _, _, hL, _, hAgree, _, hEntire, hPoles, _, hNonzero⟩ :=
    manuscriptHecke_regularities F χ S hs hu η ν μ hν t ht
  refine ⟨L, hL, hAgree, fun Φ p hΦ => ?_⟩
  let b := (t : ℂ) * I
  have hq : (1 + b).re = 1 := by simp [b, Complex.mul_re]
  have hTwo : L 2 ≠ 0 := hNonzero 2 (by norm_num) (Or.inr fun h => by
    have hre := congrArg Complex.re h
    norm_num [hq] at hre)
  have hTwoAna : AnalyticAt ℂ L 2 := by
    by_cases hw : heckeNormOneRestriction F χ = 1
    · apply (hPoles hw).2.2.1
      · intro he
        have hre := congrArg Complex.re he
        norm_num [b, Complex.mul_re] at hre
      · intro he
        have hre := congrArg Complex.re he
        norm_num [hq] at hre
    · exact hEntire hw _ (mem_univ _)
  have hTwoOrder : meromorphicOrderAt L 2 = 0 :=
    (hTwoAna.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr hTwo
  have hp := (hL.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
    ⟨⟨2, mem_univ _⟩, by simp [hTwoOrder]⟩ ⟨p, mem_univ _⟩
  let d := MeromorphicOn.divisor L univ p
  have hd : meromorphicOrderAt L p = d := by
    dsimp [d]
    rw [hL.divisor_apply (mem_univ p), WithTop.coe_untop₀_of_ne_top hp]
  change meromorphicResidue (Φ * logDeriv L) p = (↑(max d 0) : ℂ) * Φ p -
    (if heckeNormOneRestriction F χ = 1 ∧ (p = b ∨ p = 1 + b) then Φ p else 0)
  rw [meromorphicResidue_mul_logDeriv (hL p (mem_univ p)) hd hΦ]
  split_ifs with hcase
  · obtain ⟨hw, rfl | rfl⟩ := hcase
    · have h : d = -1 := WithTop.coe_injective (hd.symm.trans (hPoles hw).1)
      simp [h]
    · have h : d = -1 := WithTop.coe_injective (hd.symm.trans (hPoles hw).2.1)
      simp [h]
  · have hAna : AnalyticAt ℂ L p := by
      by_cases hw : heckeNormOneRestriction F χ = 1
      · exact (hPoles hw).2.2.1 p
          (fun h => hcase ⟨hw, Or.inl h⟩) (fun h => hcase ⟨hw, Or.inr h⟩)
      · exact hEntire hw _ (mem_univ _)
    have hn : (0 : WithTop ℤ) ≤ d := hd ▸ hAna.meromorphicOrderAt_nonneg
    exact (by rw [max_eq_left (WithTop.coe_le_coe.mp hn), sub_zero])

end

end Masullo
