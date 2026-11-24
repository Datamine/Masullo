import SLocalCarvingHilbert

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (Q F) := borel _
local instance : BorelSpace (Q F) := ⟨rfl⟩
local instance : T2Space (Q F) := ideleClasses_hausdorff
local instance : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
private abbrev μ := globalClassMeasure F ν
local instance : (μ F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν
private abbrev L := Lp ℂ 2 (μ F ν)
private abbrev H (ω : PontryaginDual (K F)) (s : ℝ) (hs : 0 ≤ s) :=
  globalOrbitalSobolevIsotype F (μ F ν) s hs ω
private abbrev P := (GlobalBruhat.polarEvaluation F).ker

private abbrev band (Λ : ℝ) (twoSided : Bool) : Set (Q F) :=
  (ideleClassNorm F) ⁻¹' (Ici Λ⁻¹ ∩ (if twoSided then Iic Λ else univ))
private abbrev ρ (Λ : ℝ) (twoSided : Bool) : Q F → ℝ :=
  (band F Λ twoSided).indicator (fun _ ↦ 1)
private abbrev r (q : Q F) := (ideleClassLogNorm F q).toAdd

private theorem band_measurable (Λ : ℝ) (twoSided : Bool) :
    MeasurableSet (band F Λ twoSided) := by
  apply (ideleClassNorm_continuous F).measurable
  cases twoSided
  · exact measurableSet_Ici.inter MeasurableSet.univ
  · exact measurableSet_Ici.inter measurableSet_Iic

private theorem band_lower (Λ : ℝ) (hΛ : 0 < Λ) (twoSided : Bool) :
    ∀ q ∈ band F Λ twoSided, Real.log Λ⁻¹ ≤ r F q := by
  intro q hq
  change Real.log Λ⁻¹ ≤ Real.log (ideleClassNorm F q)
  exact (Real.log_le_log_iff (inv_pos.mpr hΛ) (ideleClassNorm_pos F q)).mpr hq.1

private theorem band_invariant (Λ : ℝ) (twoSided : Bool) (k : K F) (q : Q F) :
    k.val⁻¹ * q ∈ band F Λ twoSided ↔ q ∈ band F Λ twoSided := by
  let I : Set ℝ := Ici Λ⁻¹ ∩ (if twoSided then Iic Λ else univ)
  change ideleClassNorm F (k.val⁻¹ * q) ∈ I ↔ ideleClassNorm F q ∈ I
  rw [map_mul, map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, one_mul]

private theorem band_nonneg (Λ : ℝ) (twoSided : Bool) (q : Q F) : 0 ≤ ρ F Λ twoSided q := by
  by_cases hq : q ∈ band F Λ twoSided
  · rw [show ρ F Λ twoSided q = 1 from indicator_of_mem hq _]
    exact zero_le_one
  · rw [show ρ F Λ twoSided q = 0 from indicator_of_notMem hq _]

private theorem band_le_one (Λ : ℝ) (twoSided : Bool) (q : Q F) : ρ F Λ twoSided q ≤ 1 := by
  by_cases hq : q ∈ band F Λ twoSided
  · rw [show ρ F Λ twoSided q = 1 from indicator_of_mem hq _]
  · rw [show ρ F Λ twoSided q = 0 from indicator_of_notMem hq _]
    exact zero_le_one

def manuscriptCarvingCutoff (Λ : ℝ) (twoSided : Bool) : L F ν →L[ℂ] L F ν :=
  cutoffOperator (ρ F Λ twoSided) (measurable_const.indicator (band_measurable F Λ twoSided))
    (band_nonneg F Λ twoSided) (band_le_one F Λ twoSided)

def manuscriptCarvingStage (ω : PontryaginDual (K F)) (s : ℝ) (hs : 0 ≤ s)
    (Λ : ℝ) (twoSided : Bool) (A : Finset (Place F)) : Set (L F ν) :=
  closure (range fun f : P F ↦ manuscriptCarvingCutoff F ν Λ twoSided
    (globalIsotypicPrincipalValues F (μ F ν) s hs ω A (globalOrbitalHomogeneousTest F ν s hs ω f)).val)

private abbrev LocalTests (S : Finset (Place F)) :=
  {f : sLocalBruhatImage F S //
    sLocalBruhatRestriction F S f.val 0 = 0 ∧
    sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val 0 = 0}

private theorem manuscriptCarvingStage_eq (ω : PontryaginDual (K F)) (s : ℝ) (hs : 0 ≤ s)
    (Λ : ℝ) (hΛ : 0 < Λ) (twoSided : Bool) (A : Finset (Place F))
    (hA : ∀ v ∈ A, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1) :
    manuscriptCarvingStage F ν ω s hs Λ twoSided A =
      range (fun z : H F ν ω s hs ↦ manuscriptCarvingCutoff F ν Λ twoSided z.val) := by
  cases twoSided
  · obtain ⟨_,_,_,h⟩ := cutoff_homogeneousPolarTests_range_closure_eq_cutoff_range F ν s hs A ω hA Λ hΛ none
    exact h
  · obtain ⟨_,_,_,h⟩ := cutoff_homogeneousPolarTests_range_closure_eq_cutoff_range F ν s hs A ω hA Λ hΛ (some Λ)
    exact h

private theorem unit_character_of_sUnramified
    (S : Finset (Place F)) (ω : PontryaginDual (K F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (Q F))))
    (v : Place F) (hv : v ∉ S) : ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 := by
  apply PontryaginDual.ext
  intro u
  let x := u.val
  have hx : x ∈ (v.adicCompletionIntegers F).toSubmonoid.units :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      ((finiteCompletion_norm_eq_one_iff F v x).mp u.property)
  have hu := (Submonoid.mem_units_iff (v.adicCompletionIntegers F).toSubmonoid x).mp hx
  let y : (v.adicCompletionIntegers F)ˣ :=
    ⟨⟨x.val,hu.1⟩,⟨x.inv,hu.2⟩,Subtype.ext x.val_inv,Subtype.ext x.inv_val⟩
  have hy : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom y = x := Units.ext rfl
  have he := (mem_sUnramified_iff F S _).mp hω v hv y
  rw [hy] at he
  let k := globalSobolevFiniteUnitInclusion F v u
  have hk : k.val = ideleClassMap F (singleFiniteIdele F v x) := finitePlaceInsertion_apply F v x
  rw [← hk, globalNormOneCharacter_apply F ω k] at he
  exact Subtype.ext he

/-- The original unramifiedness hypothesis descends to the norm-one
component, since an inserted local unit has idelic modulus one. -/
theorem normOneRestriction_sUnramified
    (S : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∉ S, unramifiedFiniteCharacter F χ v) :
    globalNormOneCharacter F (χ.comp (⟨(K F).subtype, continuous_subtype_val⟩ : K F →ₜ* Q F))
      ∈ (sUnramified F S : Set (QuasiCharacter (Q F))) := by
  let ω : PontryaginDual (K F) := χ.comp (⟨(K F).subtype, continuous_subtype_val⟩ : K F →ₜ* Q F)
  apply (mem_sUnramified_iff F S _).mpr
  intro v hv u
  let a := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
  have ha : ‖a.val‖ = 1 :=
    (finiteCompletion_norm_eq_one_iff F v a).mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        ⟨u.val.property,u.inv.property⟩)
  let k : K F := ⟨ideleClassMap F (singleFiniteIdele F v a), by
    change ideleClassNorm F (ideleClassMap F (singleFiniteIdele F v a)) = 1
    rw [ideleClassNorm_mk, singleFiniteIdele_norm, ha]⟩
  change globalNormOneCharacter F ω k.val = 1
  exact (globalNormOneCharacter_apply F ω k).trans
    (congrArg (fun z : Circle ↦ (z : ℂ)) (hχ v hv a ha))

private theorem residuePrime_eq_of_liesOver (v : Place F) (p : ℕ)
    (hv : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) : finiteResiduePrime F v = p := by
  obtain ⟨_,_,_,h, _⟩ := finiteResiduePrime_spec F v
  have he : (Ideal.span {(finiteResiduePrime F v : ℤ)} : Ideal ℤ) = Ideal.span {(p : ℤ)} :=
    h.over.trans hv.over.symm
  have h₁ := Ideal.span_singleton_le_span_singleton.mp (le_of_eq he)
  have h₂ := Ideal.span_singleton_le_span_singleton.mp (le_of_eq he.symm)
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp h₂) (Int.natCast_dvd_natCast.mp h₁)

private theorem carving_degree_pos (s : ℝ) (hs : 2 * (Module.finrank ℚ F : ℝ) ≤ s) :
    1 < s := by
  have hn : 1 ≤ Module.finrank ℚ F := Module.finrank_pos
  have h : (1 : ℝ) ≤ Module.finrank ℚ F := by exact_mod_cast hn
  linarith

set_option maxHeartbeats 1800000 in
/-- The corrected Theorem 11.1.2.1. The limit is the same closed isotype
at every cutoff stage, uncut stages are strictly nested at new rational
primes, and the fixed-cutoff limit is generated by the norm-one projections
of (11.1.2.7) with the two local zero evaluations. -/
theorem manuscriptSLocalCarving
    (S : Finset (Place F)) [Subsingleton (SPicardGroup F S)]
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∉ S, unramifiedFiniteCharacter F χ v)
    (s : ℝ) (hDegree : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
    (Λ : ℝ) (hΛ : 0 < Λ) (twoSided : Bool) :
    let ω : PontryaginDual (K F) := χ.comp (⟨(K F).subtype, continuous_subtype_val⟩ : K F →ₜ* Q F)
    let hω := normOneRestriction_sUnramified F S χ hχ
    let hs := zero_le_one.trans (carving_degree_pos F s hDegree).le
    let L₀ := (manuscriptCarvingCutoff F ν Λ twoSided).comp (H F ν ω s hs).subtypeL
    let stage := manuscriptCarvingStage F ν ω s hs Λ twoSided
    let hS := sIdeleClassInclusion_surjective_of_trivial_picard F S
    let G (f : LocalTests F S) :=
      sLocalCutoffCarvingGenerator F ν S hS ω hω s hs (band F Λ twoSided)
        (band_measurable F Λ twoSided) (Real.log Λ⁻¹) (band_lower F Λ hΛ twoSided) f.val
    IsClosed (range L₀) ∧
      (∀ (seq : ℕ → Finset (Place F)), (∀ n, Disjoint (seq n) S) →
        (⋂ n, stage (seq n)) = range L₀) ∧
      (∀ A B : Finset (Place F), A ⊆ B → Disjoint B S →
        (∃ p : ℕ, p.Prime ∧ (∃ v ∈ B, v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) ∧
          ∀ w ∈ A, ¬ w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) →
        closure (range fun f : P F ↦
          (globalIsotypicPrincipalValues F (μ F ν) s hs ω B (globalOrbitalHomogeneousTest F ν s hs ω f)).val) <
        closure (range fun f : P F ↦
          (globalIsotypicPrincipalValues F (μ F ν) s hs ω A (globalOrbitalHomogeneousTest F ν s hs ω f)).val) ∧
        stage B = stage A) ∧
      closure (Submodule.span ℂ (range G) : Set (L F ν)) = range L₀ := by
  intro ω hω hs L₀ stage hS G
  classical
  have hInv := band_invariant F Λ twoSided
  let h₀ := band_nonneg F Λ twoSided
  let h₁ := band_le_one F Λ twoSided
  have hunit := unit_character_of_sUnramified F S ω hω
  have hClosed : IsClosed (range L₀) :=
    isClosed_globalOrbitalIsotype_cutoff_range F s hs (μ F ν) ω _ (band_measurable F Λ twoSided) hInv h₀ h₁
  have hStage (A : Finset (Place F)) (hA : Disjoint A S) : stage A = range L₀ :=
    manuscriptCarvingStage_eq F ν ω s hs Λ hΛ twoSided A
      (fun v hv ↦ hunit v (fun h ↦ Finset.disjoint_left.mp hA hv h))
  refine ⟨hClosed, ?_, ?_, ?_⟩
  · intro seq hseq
    simp only [fun n ↦ hStage (seq n) (hseq n), iInter_const]
  · intro A B hAB hBS hnew
    obtain ⟨p,_,⟨v,hv,hvp⟩,hp⟩ := hnew
    have hd : ∀ w ∈ A, finiteResiduePrime F v ≠ finiteResiduePrime F w := by
      intro w hw he
      obtain ⟨_,_,_,hwp,_⟩ := finiteResiduePrime_spec F w
      rw [← he, residuePrime_eq_of_liesOver F v p hvp] at hwp
      exact hp w hw hwp
    exact ⟨homogeneousPolarTests_range_closure_lt_of_new_residuePrime F ν s hs hAB
      (carving_degree_pos F s hDegree) ω
      (fun w hw ↦ hunit w (fun hm ↦ Finset.disjoint_left.mp hBS hw hm)) v hv hd,
      (hStage B hBS).trans (hStage A (Finset.disjoint_of_subset_left hAB hBS)).symm⟩
  · have hGen : closure (range G) = range L₀ := by
      have h := sLocalCutoffCarvingGenerator_closure F ν S hS ω hω s hs _ (band_measurable F Λ twoSided)
        (Real.log Λ⁻¹) (band_lower F Λ hΛ twoSided) hInv h₀ h₁
      refine Eq.trans ?_ h
      apply congrArg closure
      ext y
      constructor
      · rintro ⟨f,rfl⟩
        exact ⟨⟨f.val,(sLocalPolarEvaluation_zero_iff F S f.val).mpr f.property⟩,rfl⟩
      · rintro ⟨f,rfl⟩
        have he : GlobalBruhat.polarEvaluation F f.val.val = 0 := f.property
        exact ⟨⟨f.val,(sLocalPolarEvaluation_zero_iff F S f.val).mp he⟩,rfl⟩
    apply le_antisymm
    · apply closure_minimal _ hClosed
      change (Submodule.span ℂ (range G) : Set (L F ν)) ⊆ (L₀.toLinearMap.range : Set (L F ν))
      apply Submodule.span_le.mpr
      exact subset_closure.trans (le_of_eq hGen)
    · rw [← hGen]
      exact closure_mono Submodule.subset_span

end
end Masullo
