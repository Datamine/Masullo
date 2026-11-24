import EntireBergmanRestriction

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000

private abbrev B := SchwartzBergman (univ : Set ℝ)

private def entireOfDifferentiable (g : ℂ → ℂ) (hg : Differentiable ℂ g) : CompactOpenEntire :=
  ⟨⟨g, hg.continuous⟩, hg⟩

/-- Translation preserves the local order of an entire function at the translated center. -/
theorem analyticOrderAt_translate_entire {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (d z : ℂ) :
    analyticOrderAt (fun w ↦ g (w + d)) z = analyticOrderAt g (z + d) := by
  have hd : AnalyticAt ℂ (fun w ↦ g (w + d)) z :=
    (hg.comp (differentiable_id.add_const d)).analyticAt z
  have h (n : ℕ) : (n : ℕ∞) ≤ analyticOrderAt (fun w ↦ g (w + d)) z ↔
      (n : ℕ∞) ≤ analyticOrderAt g (z + d) := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg.analyticAt (z + d))]
    have hd' (m : ℕ) : iteratedDeriv m (fun w ↦ g (w + d)) z = iteratedDeriv m g (z + d) :=
      congrFun (iteratedDeriv_comp_add_const m g d) z
    simp only [hd']
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    exact fun n hn ↦ (h n).mp hn
  · rw [← ENat.forall_natCast_le_iff_le]
    exact fun n hn ↦ (h n).mpr hn

/-- An entire generator viewed in its translated character chart. -/
def shiftedCompactOpenGenerator (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a : ℝ) : CompactOpenEntire :=
  entireOfDifferentiable (fun z ↦ g (z + (a : ℂ) * Complex.I))
    (hg.comp (differentiable_id.add_const _))

/-- A translated entire divisor, with its representative translated by
the same amount, has the expected orders. -/
theorem schwartzBergmanEntireShift_analyticOrderAt (b : B) (d z : ℂ) :
    analyticOrderAt (schwartzBergmanEntireShift d b).val z = analyticOrderAt b.val (z + d) := by
  have hb : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  rw [show (schwartzBergmanEntireShift d b).val = fun z ↦ b.val (z + d) from
    funext (schwartzBergmanEntireShift_apply d b)]
  exact analyticOrderAt_translate_entire hb d z

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev G (r : GlobalBruhat F) := globalHeckeClearedZeta F ν ω r

/-- The pole-cleared global reference in the norm-frequency chart. -/
def spectralShiftedGenerator (r : GlobalBruhat F) (a : ℝ) : CompactOpenEntire :=
  shiftedCompactOpenGenerator (G F ν ω r) (fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt) a

include μ hν in
/-- The cleared reference defining the jet index has the completed Euler
orders, with order zero at the two canceled trivial poles. -/
theorem exists_globalSpectral_clearedCompletedOrders (r : GlobalBruhat F)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0) z ≤
      meromorphicOrderAt (globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0) z) :
    ∃ (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (L : ℂ → ℂ),
      MeromorphicOn L univ ∧ EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      ∀ z, meromorphicOrderAt (G F ν ω r) z =
        if ω = 1 ∧ (z = 0 ∨ z = 1) then 0 else meromorphicOrderAt L z := by
  classical
  let Z (f : GlobalBruhat F) := globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨r', L, hE, hL, hLorder, _, _, hfactor⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  have hEq (z : ℂ) : meromorphicOrderAt (Z r) z = meromorphicOrderAt L z := by
    apply le_antisymm ((hmin r' z).trans (hLorder z).ge)
    obtain ⟨u, hu', he⟩ := hfactor r
    have he' : Z r =ᶠ[𝓝[≠] z] L * u := he z
    have ha := hu' z (mem_univ z)
    rw [meromorphicOrderAt_congr he', meromorphicOrderAt_mul (hL z (mem_univ z)) ha.meromorphicAt]
    exact le_add_of_nonneg_right ha.meromorphicOrderAt_nonneg
  refine ⟨S, hs, hu, L, hL, hE, fun z ↦ ?_⟩
  by_cases hz : ω = 1 ∧ (z = 0 ∨ z = 1)
  · rw [ite_eq_left hz]
    obtain ⟨hω, hz₀ | hz₁⟩ := hz
    · subst ω z
      have hn := (trivial_reference_regularized_nonzero F ν r hmin).1
      have ha := globalHeckeClearedZeta_analytic F ν 1 r 0
      rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hn]
      rfl
    · subst ω z
      have hn := (trivial_reference_regularized_nonzero F ν r hmin).2
      have ha := globalHeckeClearedZeta_analytic F ν 1 r 1
      rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hn]
      rfl
  · rw [ite_eq_right hz, globalHeckeClearedZeta_meromorphicOrder]
    have hp : globalHeckePoleFactor F ω z ≠ 0 := by
      by_cases hω : ω = 1
      · have h₀ : z ≠ 0 := fun h ↦ hz ⟨hω, Or.inl h⟩
        have h₁ : z ≠ 1 := fun h ↦ hz ⟨hω, Or.inr h⟩
        simpa only [globalHeckePoleFactor, ite_eq_left hω] using
          mul_ne_zero h₀ (sub_ne_zero.mpr h₁.symm)
      · simpa only [globalHeckePoleFactor, ite_eq_right hω] using (one_ne_zero : (1 : ℂ) ≠ 0)
    have ha := globalHeckePoleFactor_analytic F ω z
    have hpo : meromorphicOrderAt (globalHeckePoleFactor F ω) z = 0 := by
      rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hp]
      rfl
    rw [hpo, zero_add]
    exact hEq z

#print axioms schwartzBergmanEntireShift_analyticOrderAt
#print axioms exists_globalSpectral_clearedCompletedOrders

end

end Masullo
