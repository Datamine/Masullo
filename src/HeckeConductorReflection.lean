import FiniteGaussTest
import GlobalHeckeTateReflection
import ManuscriptHeckeRegularity
import LogDerivativeResidue

open Complex Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev q (v : Place F) : ℝ := v.asIdeal.absNorm
private abbrev d (v : Place F) : ℕ := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))

/-- Exponents of the finite unit filtration on which the character is trivial. -/
def finiteConductorLevels (v : Place F) (χ : (v.adicCompletion F)ˣ → Circle) : Set ℕ :=
  {n | ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
    ‖u.val - 1‖ ≤ q F v ^ (-(n : ℤ)) → χ u = 1}

theorem integralUnits_iff_norm (v : Place F) (u : (v.adicCompletion F)ˣ) :
    u ∈ finitePlaceIntegralUnits F v ↔ ‖u.val‖ = 1 := by
  have hi (z : v.adicCompletion F) : z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff.symm
  change (u.val ∈ v.adicCompletionIntegers F ∧ u.inv ∈ v.adicCompletionIntegers F) ↔ ‖u.val‖ = 1
  rw [hi, hi, show u.inv = u.val⁻¹ from Units.val_inv_eq_inv_val u, norm_inv]
  have hx : 0 < ‖u.val‖ := norm_pos_iff.mpr (Units.ne_zero u)
  constructor
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm h₁ ((inv_le_one_iff₀.mp h₂).resolve_left hx.not_ge)
  · intro h
    simp [h]

private theorem isLeast_conductor_zero (v : Place F) (χ : (v.adicCompletion F)ˣ → Circle)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 → χ u = 1) :
    IsLeast (finiteConductorLevels F v χ) 0 :=
  ⟨fun u hu _ => hχ u hu, fun _ _ => Nat.zero_le _⟩

/-- Every finite multiplier has a spectral exponent given by the different
and the exact least depth of the multiplicative character. -/
theorem finiteTateMultiplier_conductor_power
    (S : Finset (Place F))
    [∀ w : Place F, MeasurableSpace (w.adicCompletion F)]
    [∀ w : Place F, BorelSpace (w.adicCompletion F)]
    [∀ w : S, MeasurableSpace (w.val.adicCompletion F)ˣ]
    [∀ w : S, BorelSpace (w.val.adicCompletion F)ˣ]
    (μ : ∀ w : S, Measure (w.val.adicCompletion F)ˣ) [∀ w : S, (μ w).IsHaarMeasure]
    (χ : ∀ w : S, (w.val.adicCompletion F)ˣ →ₜ* Circle) (w : S) (ε : ℂ → ℂ)
    (hε : IsFiniteTateMultiplier F S μ χ w ε) :
    ∃ n : ℕ, IsLeast (finiteConductorLevels F w.val (χ w)) n ∧
      ∀ z : ℂ, ε z = ε (1 / 2) * exp (((d F w.val : ℂ) + (n : ℂ)) *
        (Real.log (q F w.val) : ℂ) * (z - 1 / 2)) := by
  by_cases hχ : finiteZetaUnramified F w.val (χ w)
  · refine ⟨0, isLeast_conductor_zero F _ _ (fun u hu =>
        hχ u ((integralUnits_iff_norm F _ u).2 hu)), fun z => ?_⟩
    obtain ⟨a, _, _, ha⟩ := hε.2.2.2.2 hχ
    rw [ha z, ha (1 / 2), ← exp_add]
    congr 1
    push_cast
    ring
  · obtain ⟨n, _, hn, htriv, ⟨u, hu, hprev, hnot⟩, _, _, _, _, hpow, _⟩ :=
      IsFiniteTateMultiplier.ramified_gauss_sum F S μ χ w ε hε hχ
    refine ⟨n, ⟨fun s _ hs => htriv s hs, ?_⟩, fun z => ?_⟩
    · intro m hm
      by_contra! hmn
      have hq : 1 ≤ q F w.val := by
        exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w.val).le
      have hcmp : q F w.val ^ (1 - (n : ℤ)) ≤ q F w.val ^ (-(m : ℤ)) :=
        zpow_le_zpow_right₀ hq (by omega)
      exact hnot (hm u hu (hprev.trans hcmp))
    · rw [hpow]
      congr 2
      ring

/-- The local conductor exponent of a global unitary idele-class character. -/
def heckeConductorExponent (χ : PontryaginDual (IdeleClass F)) (v : Place F) : ℕ :=
  sInf (finiteConductorLevels F v (fun u => χ (ideleClassMap F (singleFiniteIdele F v u))))

/-- The conductor ideal formed from the local unit-filtration depths. -/
def heckeConductorIdeal (χ : PontryaginDual (IdeleClass F)) : Ideal (𝓞 F) :=
  ∏ᶠ v : Place F, v.asIdeal ^ heckeConductorExponent F χ v

theorem heckeConductorExponent_of_unramified (χ : PontryaginDual (IdeleClass F))
    (v : Place F) (hχ : unramifiedFiniteCharacter F χ v) :
    heckeConductorExponent F χ v = 0 := by
  exact (isLeast_conductor_zero F v _ hχ).csInf_eq

theorem heckeConductorExponent_normOne (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) (v : Place F) :
    heckeConductorExponent F χ v =
      heckeConductorExponent F (normOneEulerCharacter F (heckeNormOneRestriction F χ)) v := by
  unfold heckeConductorExponent
  congr 1
  ext n
  change (∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 → ‖u.val - 1‖ ≤ _ → _) ↔ _
  have hu (u : (v.adicCompletion F)ˣ) (h : ‖u.val‖ = 1) :
      χ (ideleClassMap F (singleFiniteIdele F v u)) =
        normOneEulerCharacter F (heckeNormOneRestriction F χ) (ideleClassMap F (singleFiniteIdele F v u)) := by
    apply Circle.coe_injective
    rw [ht, ideleClassNorm_mk, singleFiniteIdele_norm, h, Real.log_one,
      ofReal_zero, mul_zero, exp_zero, mul_one]
  exact ⟨fun h u h₁ h₂ => (hu u h₁).symm.trans (h u h₁ h₂),
    fun h u h₁ h₂ => (hu u h₁).trans (h u h₁ h₂)⟩

/-- The actual finite conductor exponent is attained and is least. -/
theorem heckeConductorExponent_isLeast (χ : PontryaginDual (IdeleClass F)) (v : Place F) :
    IsLeast (finiteConductorLevels F v
      (fun u => χ (ideleClassMap F (singleFiniteIdele F v u))))
      (heckeConductorExponent F χ v) := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  let ω := heckeNormOneRestriction F χ
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  let T := insert v S
  obtain ⟨hs, hu⟩ := hS T (Finset.subset_insert _ _)
  let w : T := ⟨v, Finset.mem_insert_self _ _⟩
  let ψ := sLocalFiniteZetaPhases F T (sLocalNormOneCharacterOfGlobal F ω T hs hu) w
  obtain ⟨ρ, hρ, _, hsmall⟩ := exists_finiteGaussTest_congruenceRadius F v ψ
  have hq : 1 < q F v := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq₀.le)
    (inv_lt_one_of_one_lt₀ hq)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).2 ρ hρ).exists
  let P := finiteConductorLevels F v (fun u => χ (ideleClassMap F (singleFiniteIdele F v u)))
  have hP : P.Nonempty := by
    refine ⟨n, fun u hunit hdist => ?_⟩
    have hle : q F v ^ (-(n : ℤ)) ≤ ρ := by
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact hn.le
    have hsmall' := hsmall u (hdist.trans hle)
    apply Circle.coe_injective
    have hs' := sLocalFiniteZetaPhases_of_global F T ω hs hu w u
    rw [ht, ideleClassNorm_mk, singleFiniteIdele_norm, hunit, Real.log_one,
      ofReal_zero, mul_zero, exp_zero, mul_one]
    change globalNormOneCharacter F ω (ideleClassMap F (singleFiniteIdele F v u)) = (1 : ℂ)
    exact hs'.symm.trans (congrArg Subtype.val hsmall')
  exact ⟨Nat.sInf_mem hP, fun _ h => Nat.sInf_le h⟩

/-- Triviality persists at every deeper finite conductor level. -/
theorem finiteConductorLevels_mono (v : Place F) (χ : (v.adicCompletion F)ˣ → Circle)
    {m n : ℕ} (hm : m ∈ finiteConductorLevels F v χ) (hmn : m ≤ n) :
    n ∈ finiteConductorLevels F v χ := by
  intro u hu hdist
  have hq : 1 ≤ q F v := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  exact hm u hu (hdist.trans (zpow_le_zpow_right₀ hq (by omega)))

/-- The zero conductor level is exactly the unramified case. -/
theorem unramifiedFiniteCharacter_of_heckeConductorExponent_eq_zero
    (χ : PontryaginDual (IdeleClass F)) (v : Place F)
    (hv : heckeConductorExponent F χ v = 0) : unramifiedFiniteCharacter F χ v := by
  intro u hu
  have h := (heckeConductorExponent_isLeast F χ v).1
  rw [hv] at h
  apply h u hu
  simp only [Nat.cast_zero, neg_zero, zpow_zero]
  simpa only [sub_eq_add_neg, norm_neg, norm_one, hu, max_self] using
    (IsUltrametricDist.norm_add_le_max u.val (-(1 : v.adicCompletion F)))

/-- The norm of the conductor multiplied by the absolute discriminant. -/
def heckeDiscriminantConductor (χ : PontryaginDual (IdeleClass F)) : ℕ :=
  (discr F).natAbs * (heckeConductorIdeal F χ).absNorm

private theorem conductor_zero_off_stage (ω : PontryaginDual (K F)) (S : Finset (Place F))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (v : Place F) (hv : v ∉ S) :
    heckeConductorExponent F (normOneEulerCharacter F ω) v = 0 := by
  apply heckeConductorExponent_of_unramified
  intro u hn
  have hu' := (integralUnits_iff_norm F v u).2 hn
  let a : (v.adicCompletionIntegers F)ˣ :=
    ⟨⟨u.val, hu'.1⟩, ⟨u.inv, hu'.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
  have ha : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a = u := by
    apply Units.ext
    rfl
  apply Circle.coe_injective
  change globalNormOneCharacter F ω (ideleClassMap F (singleFiniteIdele F v u)) = 1
  rw [← ha]
  exact (mem_sUnramified_iff F S _).mp hu v hv a

/-- Only finitely many finite places contribute to the global conductor. -/
theorem heckeConductorExponent_finiteSupport (χ : PontryaginDual (IdeleClass F)) :
    (Function.support (heckeConductorExponent F χ)).Finite := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  let ω := heckeNormOneRestriction F χ
  obtain ⟨S, _, hu, _, _⟩ := exists_globalHeckeTateStage F ω
  refine S.finite_toSet.subset fun v hv => ?_
  by_contra h
  have he := (heckeConductorExponent_normOne F χ ht v).trans
    (conductor_zero_off_stage F ω S hu v h)
  exact hv he

private theorem stage_discriminantConductor_log (ω : PontryaginDual (K F)) (S : Finset (Place F))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    (∑ v ∈ S, ((d F v : ℝ) + heckeConductorExponent F (normOneEulerCharacter F ω) v) *
      Real.log (q F v)) =
      Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) := by
  let n := heckeConductorExponent F (normOneEulerCharacter F ω)
  have hq (v : Place F) : 0 < q F v := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hdo (v : Place F) (hv : v ∉ S) : d F v = 0 :=
    multiplicity_eq_zero.mpr (fun h => hv (hD v h))
  have hDprod : ∏ v ∈ S, v.asIdeal ^ d F v = differentIdeal ℤ (𝓞 F) := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (f := fun v => v.asIdeal ^ d F v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity differentIdeal_ne_bot
    · intro v hv
      by_contra hs
      exact hv (by simp [hdo v hs])
  have hCprod : ∏ v ∈ S, v.asIdeal ^ n v = heckeConductorIdeal F (normOneEulerCharacter F ω) := by
    rw [heckeConductorIdeal, finprod_eq_finsetProd_of_mulSupport_subset (s := S)]
    intro v hv
    by_contra hs
    exact hv (by simp [conductor_zero_off_stage F ω S hu v hs])
  have hNorm : (∏ v ∈ S, q F v ^ (d F v + n v)) =
      (heckeDiscriminantConductor F (normOneEulerCharacter F ω) : ℝ) := by
    have hNat : (∏ v ∈ S, v.asIdeal.absNorm ^ (d F v + n v)) =
        heckeDiscriminantConductor F (normOneEulerCharacter F ω) := by
      simpa only [map_prod, map_mul, map_pow, heckeDiscriminantConductor, absNorm_differentIdeal F (𝓞 F)] using
        congrArg (Ideal.absNorm : Ideal (𝓞 F) → ℕ) (show
          (∏ v ∈ S, v.asIdeal ^ (d F v + n v)) =
            differentIdeal ℤ (𝓞 F) * heckeConductorIdeal F (normOneEulerCharacter F ω) by
          simp only [pow_add, Finset.prod_mul_distrib, hDprod, hCprod])
    exact_mod_cast hNat
  rw [← hNorm, Real.log_prod (fun v _ => pow_ne_zero _ (hq v).ne')]
  apply Finset.sum_congr rfl
  intro v _
  rw [Real.log_pow, Nat.cast_add]

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The global Tate reflection multiplier is exponential with slope equal
to the logarithm of the discriminant–conductor product. -/
theorem exists_globalCompletedHecke_conductorReflection
    (ω : PontryaginDual (K F)) (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hu' : globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    ∃ (L L' : ℂ → ℂ) (A : ℂ),
      MeromorphicOn L univ ∧ MeromorphicOn L' univ ∧
      EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      EqOn L' (globalCompletedHeckeEuler F ω⁻¹ S hs hu') {z | 1 < z.re} ∧ A ≠ 0 ∧
      let k := (Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) : ℂ)
      ∀ c, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] fun z ↦ L z * (A * exp (k * (z - 1 / 2))) := by
  obtain ⟨L, L', ε, hL, hL', he, he', _, hε0, ⟨e, A, _, hlocal, hε⟩, _, hRef⟩ :=
    exists_globalCompletedHecke_tateReflection F S hs ω hu hu' η ν μ hν hD
  let n := heckeConductorExponent F (normOneEulerCharacter F ω)
  let k (v : Place F) := ((d F v : ℂ) + n v) * (Real.log (q F v) : ℂ)
  have hPower (w : S) (z : ℂ) : e w z = e w (1 / 2) * exp (k w * (z - 1 / 2)) := by
    obtain ⟨m, hm, hpow⟩ := finiteTateMultiplier_conductor_power F S (fun w : S ↦ μ w.val) _ w (e w)
      (hlocal w)
    have hLevels : finiteConductorLevels F w.val
        (sLocalFiniteZetaPhases F S (sLocalNormOneCharacterOfGlobal F ω S hs hu) w) =
        finiteConductorLevels F w.val
          (fun u => normOneEulerCharacter F ω (ideleClassMap F (singleFiniteIdele F w.val u))) := by
      congr 1
      funext u
      apply Circle.coe_injective
      exact sLocalFiniteZetaPhases_of_global F S ω hs hu w u
    have hn : n w = m := by
      rw [hLevels] at hm
      exact hm.csInf_eq
    simpa only [k, hn, mul_assoc] using hpow z
  have hsum : (∑ v : S, k v) =
      (Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) : ℂ) := by
    change (∑ v ∈ S.attach, k v.val) = _
    rw [Finset.sum_attach]
    simpa only [ofReal_sum, ofReal_add, ofReal_natCast, ofReal_mul, k, n] using
      congrArg (fun x : ℝ => (x : ℂ)) (stage_discriminantConductor_log F ω S hu hD)
  refine ⟨L, L', ε (1 / 2), hL, hL', he, he', hε0 _, fun c => ?_⟩
  have hExp (z : ℂ) : ε z = ε (1 / 2) *
      exp ((Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) : ℂ) * (z - 1 / 2)) := by
    rw [hε]
    unfold sLocalTateEpsilonProduct
    dsimp only
    rw [show (∏ w : S, e w z) = ∏ w : S, e w (1 / 2) * exp (k w * (z - 1 / 2)) from
      Finset.prod_congr rfl (fun w _ => hPower w z)]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.sum_mul, hsum, mul_assoc]
    simp only [mul_assoc]
  filter_upwards [hRef c] with z hz
  exact hz.trans (congrArg (L z * ·) (hExp z))

theorem logDeriv_conductor_multiplier (A k : ℂ) (hA : A ≠ 0) (s : ℂ) :
    logDeriv (fun z ↦ A * exp (k * (z - 1 / 2))) s = k := by
  let g (z : ℂ) := k * (z - 1 / 2)
  have hg : HasDerivAt g k s := by
    have h := ((hasDerivAt_id s).sub_const (1 / 2)).const_mul k
    change HasDerivAt g (k * 1) s at h
    simpa only [mul_one] using h
  change logDeriv (fun z ↦ A * (exp ∘ g) z) s = k
  rw [logDeriv_const_mul _ _ hA, logDeriv_comp (Complex.differentiableAt_exp) hg.differentiableAt,
    Complex.logDeriv_exp, Pi.one_apply, one_mul, hg.deriv]

include μ hν in
/-- The completed Hecke functional equation in the original height chart
has the conductor slope and the associated reflected logarithmic derivative. -/
theorem exists_manuscriptCompletedHecke_conductorReflection
    (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ (T : Finset (Place F)) (hT : Surjective (sIdeleClassInclusion F T))
      (hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
        (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
      (L L' : ℂ → ℂ) (A : ℂ),
      MeromorphicOn L univ ∧ MeromorphicOn L' univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      EqOn L' (manuscriptCompletedHeckeEuler F χ⁻¹ T hT hu' (-t)) {z | 1 < z.re} ∧ A ≠ 0 ∧
      let k := (Real.log (heckeDiscriminantConductor F χ) : ℂ)
      (∀ c, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] fun z ↦ L z * (A * exp (k * (z - 1 / 2)))) ∧
      ∀ s, AnalyticAt ℂ L s → AnalyticAt ℂ L' (1 - s) → L s ≠ 0 →
        logDeriv L s = -logDeriv L' (1 - s) - k := by
  let ω := heckeNormOneRestriction F χ
  obtain ⟨T, hT, hU, hU', hD⟩ := exists_globalHeckeTateStage F ω
  obtain ⟨M, M', B, hM, hM', hAgree, hAgree', hB, hRef⟩ :=
    exists_globalCompletedHecke_conductorReflection F η ν μ hν ω T hT hU hU' hD
  have hω : heckeNormOneRestriction F χ⁻¹ = ω⁻¹ := heckeNormOneRestriction_inv F χ
  have hUdual : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
      (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) := by
    rwa [hω]
  have hDual : EqOn M' (globalCompletedHeckeEuler F (heckeNormOneRestriction F χ⁻¹) T hT hUdual)
      {z | 1 < z.re} := by
    revert hUdual
    rw [hω]
    exact fun _ => hAgree'
  have hC : heckeDiscriminantConductor F χ = heckeDiscriminantConductor F (normOneEulerCharacter F ω) := by
    unfold heckeDiscriminantConductor heckeConductorIdeal
    simp_rw [heckeConductorExponent_normOne F χ ht]
    rfl
  let b := (t : ℂ) * I
  let C := (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F
  let L (z : ℂ) := C * M (z - b)
  let L' (z : ℂ) := C * M' (z + b)
  let k := (Real.log (heckeDiscriminantConductor F χ) : ℂ)
  let A := B * exp (-k * b)
  have hA : A ≠ 0 := mul_ne_zero hB (exp_ne_zero _)
  have hL : MeromorphicOn L univ := fun z _ =>
    (MeromorphicAt.const C z).mul ((hM _ (mem_univ _)).comp_analyticAt
      (g := fun w : ℂ => w - b) (analyticAt_id.sub analyticAt_const))
  have hL' : MeromorphicOn L' univ := fun z _ =>
    (MeromorphicAt.const C z).mul ((hM' _ (mem_univ _)).comp_analyticAt
      (g := fun w : ℂ => w + b) (analyticAt_id.add analyticAt_const))
  have hActualRef (c : ℂ) : (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c]
      (fun z ↦ L z * (A * exp (k * (z - 1 / 2)))) := by
    have hmap := tendsto_sub_punctured b (c - b)
    rw [sub_add_cancel] at hmap
    filter_upwards [hmap.eventually (hRef (c-b))] with z hz
    have hArg : 1 - z + b = 1 - (z - b) := by ring
    change M' (1 - (z-b)) = M (z-b) * (B * exp
      ((Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) : ℂ) * (z-b-1/2))) at hz
    change C * M' ((1-z)+b) = C * M (z-b) * (A * exp (k * (z-1/2)))
    rw [hArg, hz, ← hC]
    dsimp only [A]
    rw [mul_assoc B, ← exp_add]
    rw [show -k * b + k * (z - 1 / 2) = k * (z - b - 1 / 2) by ring]
    simp only [mul_assoc]
    rfl
  refine ⟨T, hT, hUdual, L, L', A, hL, hL', ?_, ?_, hA, hActualRef, ?_⟩
  · rw [manuscriptCompletedHeckeEuler_stage_eq F χ S hs hu t ht T hT hU]
    intro z hz
    rw [manuscriptCompletedHeckeEuler_shift F χ T hT hU t ht]
    change C * M (z - b) = C * globalCompletedHeckeEuler F ω T hT hU (z - b)
    rw [hAgree (show 1 < (z-b).re by simpa [b, Complex.sub_re, Complex.mul_re] using hz)]
  · intro z hz
    rw [manuscriptCompletedHeckeEuler_shift F χ⁻¹ T hT hUdual (-t) (HasHeckeHeight.inv F ht)]
    have hz' : z - ((-t : ℝ) : ℂ) * I = z+b := by push_cast; dsimp [b]; ring
    change C * M' (z + b) = C * globalCompletedHeckeEuler F (heckeNormOneRestriction F χ⁻¹)
      T hT hUdual (z - ((-t : ℝ) : ℂ) * I)
    rw [hz', hDual (show 1 < (z+b).re by simpa [b, Complex.add_re, Complex.mul_re] using hz)]
  · intro s hAs hAs' hLs
    let E (z : ℂ) := A * exp (k * (z - 1 / 2))
    have hE : AnalyticAt ℂ E s := by
      unfold E
      fun_prop
    have hE0 : E s ≠ 0 := mul_ne_zero hA (exp_ne_zero _)
    have h := logDeriv_of_reflection hAs hAs' hE hLs hE0 (hActualRef s)
    rw [h, logDeriv_conductor_multiplier A k hA]

end

end Masullo
