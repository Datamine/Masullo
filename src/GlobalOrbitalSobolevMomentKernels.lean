import OrbitalSobolevMomentCovariance
import GlobalSobolevWeilExtension
import GlobalThetaZeroLineDensity

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical InnerProductSpace NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance orbitalKernelsMeasurable : MeasurableSpace (Q F) := borel _
local instance orbitalKernelsBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance orbitalKernelsLocallyCompact : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance orbitalKernelsT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance orbitalKernelsSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev N := globalThetaSobolevCompletion F μ 0 0 0 s hs

private abbrev T (g : Q F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs g

private abbrev root (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F))
    (z : ℂ) (v : Place F) : Prop :=
  ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 ∧
    orbitalMomentPhase F χ z (globalUniformizerClass F v) = 1

/-- The actual Weil product contributes a vanishing factor only at places
where unit averaging acts as the identity on the given isotype. -/
def globalWeilMomentMultiplicity (S : Finset (Place F)) (ω : PontryaginDual (K F))
    (χ : PontryaginDual (Q F)) (z : ℂ) : ℕ :=
  (S.filter (root F ω χ z)).card

private theorem phase_of_uniformizer (χ : PontryaginDual (Q F)) (z : ℂ) (v : Place F) :
    orbitalMomentPhase F χ z (globalUniformizerClass F v) =
      (χ (globalUniformizerClass F v) : ℂ) *
        Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
  have h : (ideleClassLogNorm F (globalUniformizerClass F v)).toAdd =
      -Real.log (v.asIdeal.absNorm : ℝ) := by
    change Real.log (ideleClassNorm F (ideleClassMap F
      (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) = _
    rw [ideleClassNorm_mk, singleFiniteIdele_norm,
      norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv]
  unfold orbitalMomentPhase
  have he : z * ((ideleClassLogNorm F (globalUniformizerClass F v)).toAdd : ℂ) =
      -z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
    rw [h, Complex.ofReal_neg, mul_neg, neg_mul]
  rw [he]

/-- On the unramified isotype the multiplicity is the analytic order of
the manuscript's reciprocal finite Euler product. -/
theorem globalWeilMomentMultiplicity_eq_eulerOrder (S : Finset (Place F))
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F)) (z : ℂ)
    (hω : ∀ v ∈ S, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1) :
    (globalWeilMomentMultiplicity F S ω χ z : ℕ∞) =
      analyticOrderAt (orbitalEulerDenominator F S χ) z := by
  rw [orbitalEulerDenominator_order_eq_card]
  unfold globalWeilMomentMultiplicity
  congr 2
  apply Finset.filter_congr
  intro v hv
  change (ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 ∧
      orbitalMomentPhase F χ z (globalUniformizerClass F v) = 1) ↔ _
  constructor
  · rintro ⟨_, hp⟩
    exact sub_eq_zero.mpr (((phase_of_uniformizer F χ z v).symm.trans hp).symm)
  · intro hp
    exact ⟨hω v hv, (phase_of_uniformizer F χ z v).trans (sub_eq_zero.mp hp).symm⟩

/-- Finite-unit averaging selects exactly the places where the global
character is unramified. -/
theorem globalSobolevFiniteUnitInclusion_trivial_iff
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ k : K F, ω k = χ k.val) (v : Place F) :
    ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 ↔ unramifiedFiniteCharacter F χ v := by
  constructor
  · intro hu u hnorm
    let k := globalSobolevFiniteUnitInclusion F v ⟨u, hnorm⟩
    have he : k.val = ideleClassMap F (singleFiniteIdele F v u) := finitePlaceInsertion_apply F v u
    have hw : ω k = 1 := DFunLike.congr_fun hu ⟨u, hnorm⟩
    exact (congrArg χ he).symm.trans ((hχ k).symm.trans hw)
  · intro hu
    apply PontryaginDual.ext
    intro u
    let k := globalSobolevFiniteUnitInclusion F v u
    have he : k.val = ideleClassMap F (singleFiniteIdele F v u.val) := finitePlaceInsertion_apply F v u.val
    change ω k = 1
    exact (hχ k).trans ((congrArg χ he).trans (hu u.val u.property))

/-- Ramified places contribute the identity to the Weil product and have
no roots in the reciprocal Euler denominator. -/
theorem globalWeilMomentMultiplicity_eq_unramifiedEulerOrder (S : Finset (Place F))
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ k : K F, ω k = χ k.val) (z : ℂ) :
    (globalWeilMomentMultiplicity F S ω χ z : ℕ∞) =
      analyticOrderAt (orbitalEulerDenominator F (S.filter (unramifiedFiniteCharacter F χ)) χ) z := by
  let D := S.filter (unramifiedFiniteCharacter F χ)
  have hD : ∀ v ∈ D, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 :=
    fun v hv ↦ (globalSobolevFiniteUnitInclusion_trivial_iff F ω χ hχ v).mpr (Finset.mem_filter.mp hv).2
  rw [← globalWeilMomentMultiplicity_eq_eulerOrder F D ω χ z hD]
  unfold globalWeilMomentMultiplicity
  congr 2
  ext v
  simp only [Finset.mem_filter, D, root]
  constructor
  · rintro ⟨hv, hω, hz⟩
    exact ⟨⟨hv, (globalSobolevFiniteUnitInclusion_trivial_iff F ω χ hχ v).mp hω⟩, hω, hz⟩
  · rintro ⟨⟨hv, _⟩, hω, hz⟩
    exact ⟨hv, hω, hz⟩

private abbrev M (χ : PontryaginDual (Q F)) (z : ℂ) (u : Lp ℂ 2 μ) (m : ℕ) :=
  ∫ q, u q * orbitalSobolevMoment F χ s z m q ∂μ

/-- Every vector in the actual finite Weil product image has vanishing
moments up to the counted Euler multiplicity, at every admissible order. -/
theorem globalWeilProduct_moment_zero (S : Finset (Place F)) (ω : PontryaginDual (K F))
    (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (u : N F μ s hs) (hu : u.val ∈ globalAmbientSobolevIsotype F ω μ 0 0 s hs)
    (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2)
    (hcount : m < globalWeilMomentMultiplicity F S ω χ z) :
    M F μ s χ z (globalThetaSobolevWeilPrincipalValues F μ s hs S u).val m = 0 := by
  classical
  induction S using Finset.induction_on generalizing m with
  | empty =>
    simp [globalWeilMomentMultiplicity] at hcount
  | @insert v S hv ih =>
    let y := globalThetaSobolevWeilPrincipalValues F μ s hs S u
    have hy := globalThetaSobolevWeilPrincipalValues_preserves_isotype F μ s hs S ω u hu
    have hW : globalThetaSobolevWeilPrincipalValues F μ s hs (insert v S) =
        (globalThetaSobolevWeilPrincipalValue F μ s hs v).comp
          (globalThetaSobolevWeilPrincipalValues F μ s hs S) :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ hv
    rw [hW, ContinuousLinearMap.comp_apply]
    change M F μ s χ z (globalSobolevWeilPrincipalValue F μ s hs v y.val) m = 0
    rw [globalSobolevWeilPrincipalValue_of_isotype F μ s hs v ω y.val hy]
    have hend : globalWeilMomentMultiplicity F (insert v S) ω χ z =
        if root F ω χ z v then globalWeilMomentMultiplicity F S ω χ z + 1
        else globalWeilMomentMultiplicity F S ω χ z := by
      unfold globalWeilMomentMultiplicity
      rw [Finset.filter_insert]
      split
      · rw [Finset.card_insert_of_notMem (fun he ↦ hv (Finset.mem_filter.mp he).1)]
      · rfl
    rw [hend] at hcount
    by_cases hω : ω.comp (globalSobolevFiniteUnitInclusion F v) = 1
    · rw [ite_eq_left hω]
      change M F μ s χ z (y.val - T F μ s hs (globalUniformizerClass F v) y.val) m = 0
      apply orbitalSobolevMoment_difference_zero F μ s hs χ z hz (globalUniformizerClass F v) y.val m hm
      · intro j hj
        apply ih j (lt_of_le_of_lt (by exact_mod_cast hj.le) hm)
        split at hcount <;> omega
      · by_cases hp : orbitalMomentPhase F χ z (globalUniformizerClass F v) = 1
        · exact Or.inl hp
        · exact Or.inr (ih m hm (by simpa only [root, hp, and_false, ite_false] using hcount))
    · rw [ite_eq_right hω]
      exact ih m hm (by simpa only [root, hω, false_and, ite_false] using hcount)

/-- The closed image of the bounded Weil product on an isotype is
contained in the common kernel of its admissible orbital moments. -/
theorem globalClosedWeilIsotypeRange_moment_zero (S : Finset (Place F))
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2)
    (hcount : m < globalWeilMomentMultiplicity F S ω χ z) (x : Lp ℂ 2 μ)
    (hx : x ∈ closure (range fun u : globalOrbitalSobolevIsotype F μ s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F μ s hs S ⟨u.val, u.property.1⟩).val)) :
    orbitalSobolevMomentCLM F μ s hs χ z hz m hm x = 0 := by
  let L := orbitalSobolevMomentCLM F μ s hs χ z hz m hm
  apply (closure_minimal (t := {x | L x = 0}) _ (isClosed_eq L.continuous continuous_const)) hx
  rintro _ ⟨u, rfl⟩
  change L _ = 0
  rw [orbitalSobolevMomentCLM_apply]
  exact globalWeilProduct_moment_zero F μ s hs S ω χ z hz ⟨u.val, u.property.1⟩
    u.property.2 m hm hcount

/-- The source's degree hypothesis makes every moment strictly below
the actual Euler multiplicity continuous. -/
theorem globalWeilMoment_admissible (S : Finset (Place F))
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F)) (z : ℂ)
    (hS : 2 * (S.card : ℝ) ≤ s) (m : ℕ) (hm : m < globalWeilMomentMultiplicity F S ω χ z) :
    (m : ℝ) < (s - 1) / 2 := by
  have hcard : globalWeilMomentMultiplicity F S ω χ z ≤ S.card :=
    Finset.card_filter_le _ _
  have h : (m : ℝ) + 1 ≤ S.card := by
    exact_mod_cast (Nat.succ_le_of_lt (hm.trans_le hcard))
  linarith

/-- Every moment defined by a root of the reciprocal Euler product,
through the degree just below its multiplicity, vanishes on the closed
Weil range at the source's Sobolev degree. -/
theorem globalClosedWeilIsotypeRange_eulerMoment_zero (S : Finset (Place F))
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (hS : 2 * (S.card : ℝ) ≤ s)
    (hω : ∀ v ∈ S, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (m : ℕ) (hm : (m : ℕ∞) < analyticOrderAt (orbitalEulerDenominator F S χ) z)
    (x : Lp ℂ 2 μ)
    (hx : x ∈ closure (range fun u : globalOrbitalSobolevIsotype F μ s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F μ s hs S ⟨u.val, u.property.1⟩).val)) :
    M F μ s χ z x m = 0 := by
  rw [← globalWeilMomentMultiplicity_eq_eulerOrder F S ω χ z hω] at hm
  have hcount : m < globalWeilMomentMultiplicity F S ω χ z := by exact_mod_cast hm
  have had := globalWeilMoment_admissible F s S ω χ z hS m hcount
  exact (orbitalSobolevMomentCLM_apply F μ s hs χ z hz m had x).symm.trans
    (globalClosedWeilIsotypeRange_moment_zero F μ s hs S ω χ z hz m had hcount x hx)

set_option maxHeartbeats 900000 in
/-- If exactly one of two unramified places hits the frequency, the first
moment of the actual two-place product is nonzero for any input with a
nonzero zeroth moment. Thus the total number of places cannot replace
the multiplicity at the frequency in the kernel conditions. -/
theorem globalWeilProduct_pair_firstMoment_ne_zero
    (v w : Place F) (hvw : v ≠ w)
    (ω : PontryaginDual (K F)) (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (hv : ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (hw : ω.comp (globalSobolevFiniteUnitInclusion F w) = 1)
    (hzv : orbitalMomentPhase F χ z (globalUniformizerClass F v) = 1)
    (hzw : orbitalMomentPhase F χ z (globalUniformizerClass F w) ≠ 1)
    (hm : ((1 : ℕ) : ℝ) < (s - 1) / 2)
    (u : N F μ s hs) (hu : u.val ∈ globalAmbientSobolevIsotype F ω μ 0 0 s hs)
    (hu₀ : M F μ s χ z u.val 0 ≠ 0) :
    M F μ s χ z (globalThetaSobolevWeilPrincipalValues F μ s hs {v, w} u).val 1 ≠ 0 := by
  classical
  let P := globalThetaSobolevWeilPrincipalValue F μ s hs
  let y := P w u
  have hwmem : v ∉ ({w} : Finset (Place F)) := fun h ↦ hvw (Finset.mem_singleton.mp h)
  have hpair : globalThetaSobolevWeilPrincipalValues F μ s hs {v, w} = (P v).comp (P w) := by
    calc
      _ = (P v).comp (globalThetaSobolevWeilPrincipalValues F μ s hs {w}) :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ hwmem
      _ = _ := congrArg ((P v).comp) (Finset.noncommProd_singleton _ _)
  have hy : y.val ∈ globalAmbientSobolevIsotype F ω μ 0 0 s hs :=
    globalSobolevWeilPrincipalValue_mapsTo_isotype F μ s hs w ω hu
  have h₁ : y.val = u.val - T F μ s hs (globalUniformizerClass F w) u.val := by
    change globalSobolevWeilPrincipalValue F μ s hs w u.val = _
    rw [globalSobolevWeilPrincipalValue_of_isotype F μ s hs w ω u.val hu, ite_eq_left hw]
    rfl
  have h₂ : (P v y).val = y.val - T F μ s hs (globalUniformizerClass F v) y.val := by
    change globalSobolevWeilPrincipalValue F μ s hs v y.val = _
    rw [globalSobolevWeilPrincipalValue_of_isotype F μ s hs v ω y.val hy, ite_eq_left hv]
    rfl
  rw [hpair, ContinuousLinearMap.comp_apply]
  change M F μ s χ z (P v y).val 1 ≠ 0
  rw [h₂, h₁]
  have he := orbitalSobolevMoment_two_differences_first F μ s hs χ z hz
    (globalUniformizerClass F v) (globalUniformizerClass F w) u.val hm hzv
  change M F μ s χ z _ 1 = _ at he
  rw [he]
  have hlog : (ideleClassLogNorm F (globalUniformizerClass F v)).toAdd ≠ 0 := by
    change Real.log (ideleClassNorm F (ideleClassMap F
      (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) ≠ 0
    rw [ideleClassNorm_mk, singleFiniteIdele_norm,
      norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv, neg_ne_zero]
    exact (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).ne'
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlog))
    (sub_ne_zero.mpr hzw.symm)) hu₀

/-- On the actual trivial isotype, the zeroth orbital moment at each
imaginary exponent has a nonzero value. -/
theorem exists_globalTrivialIsotype_zerothMoment_ne_zero
    (z : ℂ) (hz : z.re = 0) (hdeg : 1 < s) :
    ∃ u : N F μ s hs, u.val ∈ globalAmbientSobolevIsotype F 1 μ 0 0 s hs ∧
      M F μ s 1 z u.val 0 ≠ 0 := by
  let f := orbitalSobolevMoment F 1 s z 0
  have hdeg' : ((0 : ℕ) : ℝ) < (s - 1) / 2 := by norm_num; linarith
  let hf := ((orbitalSobolevMoment_memLp_iff F μ 1 hs hz 0).mpr hdeg').star
  let v := hf.toLp (fun q ↦ star (f q))
  have hvae : (v : Q F → ℂ) =ᵐ[μ] (fun q ↦ star (f q)) := hf.coeFn_toLp
  let w : N F μ s hs := ⟨v, globalThetaSobolevMap_zeroLine_dense_of_haar F μ s hs v⟩
  refine ⟨w, ?_, ?_⟩
  · change v ∈ globalAmbientSobolevIsotype F 1 μ 0 0 s hs
    apply (mem_thetaCharacterSubspace _ _ _).mpr
    intro k
    change T F μ s hs k.val v = (1 : ℂ) • v
    rw [one_smul]
    apply Lp.ext
    filter_upwards [hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 s hs k.val v, hvae,
      (measurePreserving_mul_left μ k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hvae] with q hT hq hshift
    let a (q : Q F) := hardySobolevAmplitude 0 0 s (ideleClassLogNorm F q).toAdd
    have hk : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = Multiplicative.ofAdd 0
      rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
    have ha : a (k.val⁻¹ * q) = a q := by simp [a, map_mul, map_inv, hk]
    have hp : 0 < a q := by
      dsimp [a, hardySobolevAmplitude]
      apply Real.sqrt_pos.mpr
      unfold hardySobolevWeight
      positivity
    have hf' : f (k.val⁻¹ * q) = f q := by
      have h := orbitalSobolevMoment_isotypic F 1 s z 0 q k⁻¹
      change f (q * k.val⁻¹) = ((1 : PontryaginDual (Q F)) _ : ℂ) * f q at h
      simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, mul_comm q] using h
    change T F μ s hs k.val v q = v q
    change T F μ s hs k.val v q = ((a q / a (k.val⁻¹ * q) : ℝ) : ℂ) * v (k.val⁻¹ * q) at hT
    change v (k.val⁻¹ * q) = star (f (k.val⁻¹ * q)) at hshift
    rw [hT, ha, div_self hp.ne', Complex.ofReal_one, one_mul, hshift, hq, hf']
  · have hne (q : Q F) : f q ≠ 0 := by
      unfold f orbitalSobolevMoment
      simp only [pow_zero, mul_one, PontryaginDual.one_apply, Circle.coe_one, one_mul]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne')
        (Complex.exp_ne_zero _)
    have hv : v ≠ 0 := by
      intro hzv
      have he : ∀ᵐ q ∂μ, f q = 0 := by
        filter_upwards [hvae, Lp.coeFn_zero ℂ 2 μ] with q hq hq₀
        rw [hzv, hq₀] at hq
        exact star_eq_zero.mp hq.symm
      obtain ⟨q, hq⟩ := he.exists
      exact hne q hq
    have he := orbitalSobolevMomentCLM_apply F μ s hs 1 z hz 0 hdeg' v
    change ⟪v,v⟫_ℂ = M F μ s 1 z w.val 0 at he
    exact he ▸ inner_self_ne_zero.mpr hv

private theorem trivial_phase_eq_one_iff_eulerPole (v : Place F) (z : ℂ) :
    orbitalMomentPhase F 1 z (globalUniformizerClass F v) = 1 ↔
      v ∈ globalFiniteHeckeEulerPoles F 1 z := by
  have hq : 0 < (v.asIdeal.absNorm : ℝ) :=
    zero_lt_one.trans (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  have he : (v.asIdeal.absNorm : ℂ) ^ (-z) =
      Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
      Complex.ofReal_log hq.le, mul_comm]
  have hu : unramifiedFiniteCharacter F (1 : PontryaginDual (Q F)) v :=
    fun _ _ ↦ PontryaginDual.one_apply _
  change _ ↔ ((1 - heckeEulerCoefficient F 1 (chosenFiniteUniformizer F) v *
      (v.asIdeal.absNorm : ℂ) ^ (-z))⁻¹)⁻¹ = 0
  rw [phase_of_uniformizer, inv_inv, he, heckeEulerCoefficient, ite_eq_left hu]
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul]
  exact eq_comm.trans sub_eq_zero.symm

/-- The manuscript's total-place first-moment condition fails for two
places of distinct residue characteristic at every Sobolev degree at least four. -/
theorem exists_globalWeilProduct_pair_firstMoment_counterexample
    (hs4 : 4 ≤ s) (v w : Place F) (hvw : finiteResiduePrime F v ≠ finiteResiduePrime F w) :
    ∃ z : ℂ, z.re = 0 ∧
      orbitalMomentPhase F 1 z (globalUniformizerClass F v) = 1 ∧
      orbitalMomentPhase F 1 z (globalUniformizerClass F w) ≠ 1 ∧
      ∃ u : N F μ s hs, u.val ∈ globalAmbientSobolevIsotype F 1 μ 0 0 s hs ∧
        M F μ s 1 z (globalThetaSobolevWeilPrincipalValues F μ s hs {v,w} u).val 1 ≠ 0 := by
  let d := Real.log (v.asIdeal.absNorm : ℝ)
  have hd : 0 < d := Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  let z : ℂ := -((2 * Real.pi / d : ℝ) : ℂ) * Complex.I
  have hz : z.re = 0 := by simp [z, Complex.mul_re]
  have hz₀ : z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    (div_pos Real.two_pi_pos hd).ne')) Complex.I_ne_zero
  have hphase : orbitalMomentPhase F 1 z (globalUniformizerClass F v) = 1 := by
    rw [phase_of_uniformizer, PontryaginDual.one_apply, Circle.coe_one, one_mul]
    change Complex.exp (-z * (d : ℂ)) = 1
    have he : -z * (d : ℂ) = (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
      have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
      dsimp [z]
      push_cast
      field_simp
      ring
    rw [he, Complex.exp_add, Complex.exp_pi_mul_I]
    norm_num
  have hzeroPhase (u : Place F) : orbitalMomentPhase F 1 0 (globalUniformizerClass F u) = 1 := by
    simp [orbitalMomentPhase, PontryaginDual.one_apply]
  have hnphase : orbitalMomentPhase F 1 z (globalUniformizerClass F w) ≠ 1 := by
    intro h
    apply hz₀
    apply (globalFiniteHeckeEuler_commonPoles F 1 v w hvw)
    · exact ⟨(trivial_phase_eq_one_iff_eulerPole F v z).mp hphase,
        (trivial_phase_eq_one_iff_eulerPole F w z).mp h⟩
    · exact ⟨(trivial_phase_eq_one_iff_eulerPole F v 0).mp (hzeroPhase v),
        (trivial_phase_eq_one_iff_eulerPole F w 0).mp (hzeroPhase w)⟩
  obtain ⟨u, hu, hu₀⟩ := exists_globalTrivialIsotype_zerothMoment_ne_zero F μ s hs z hz (by linarith)
  have hun (u : Place F) : (1 : PontryaginDual (K F)).comp (globalSobolevFiniteUnitInclusion F u) = 1 := by
    apply PontryaginDual.ext
    intro k
    rfl
  refine ⟨z, hz, hphase, hnphase, u, hu, ?_⟩
  apply globalWeilProduct_pair_firstMoment_ne_zero F μ s hs v w
    (fun he ↦ hvw (congrArg (finiteResiduePrime F) he)) 1 1 z hz
    (hun v) (hun w) hphase hnphase _ u hu hu₀
  norm_num
  linarith

end
end Masullo
