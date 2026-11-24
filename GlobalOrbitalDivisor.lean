import GlobalSpectralBiorthogonal

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev Place (F : Type*) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev B := SchwartzBergman (univ : Set ℝ)

section Euler

variable (ξ : PontryaginDual (IdeleClass F))

private abbrev P := finiteHeckeOmissionMultiplier F ξ

private theorem omission_prod_singletons (W : Finset (Place F)) :
    P F ξ W = fun z ↦ ∏ v ∈ W, P F ξ {v} z := by
  funext z
  simp only [P, finiteHeckeOmissionMultiplier, Finset.prod_singleton]

/-- Each reciprocal local factor contributes order one at a zero and
order zero elsewhere. A ramified factor is identically one. -/
theorem finiteHeckeOmissionSingleton_order (v : Place F) (z : ℂ) :
    analyticOrderAt (P F ξ {v}) z = if P F ξ {v} z = 0 then 1 else 0 := by
  let A := P F ξ {v}
  let c := heckeEulerCoefficient F ξ (chosenFiniteUniformizer F) v
  let d := Real.log (v.asIdeal.absNorm : ℝ)
  have hA := finiteHeckeOmissionMultiplier_analytic F ξ {v} z
  by_cases hz : A z = 0
  · rw [ite_eq_left hz]
    have hcanonical : A = fun z ↦ 1 - c * Complex.exp (-(d : ℂ) * z) :=
      funext (euler_singleton_exp F ξ v)
    have hc : c ≠ 0 := by
      intro hc
      have he := congrFun hcanonical z
      simp [hz, hc] at he
    have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos
      (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).ne'
    have hder : deriv A z ≠ 0 := by
      rw [hcanonical]
      apply ((((hasDerivAt_id z).const_mul (-(d : ℂ))).cexp.const_mul c).const_sub 1).deriv.trans_ne
      simp [hc, hd]
    exact hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hder
  · rw [ite_eq_right hz]
    exact hA.analyticOrderAt_eq_zero.mpr hz

/-- Count each selected place at a common zero. The count includes
collisions between places of unrelated residue characteristic. -/
theorem finiteHeckeOmissionMultiplier_order (W : Finset (Place F)) (z : ℂ) :
    analyticOrderAt (P F ξ W) z = ((W.filter fun v ↦ P F ξ {v} z = 0).card : ℕ∞) := by
  induction W using Finset.induction_on with
  | empty =>
    have he : P F ξ ∅ = fun _ ↦ 1 := by
      rw [omission_prod_singletons]
      funext z
      simp
    rw [he, (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z).analyticOrderAt_eq_zero.mpr
      one_ne_zero]
    simp
  | insert v W hv ih =>
    have hE : P F ξ (insert v W) = P F ξ {v} * P F ξ W := by
      funext t
      calc
        P F ξ (insert v W) t = ∏ i ∈ insert v W, P F ξ {i} t :=
          congrFun (omission_prod_singletons F ξ (insert v W)) t
        _ = P F ξ {v} t * ∏ i ∈ W, P F ξ {i} t := Finset.prod_insert hv
        _ = (P F ξ {v} * P F ξ W) t :=
          congrArg (P F ξ {v} t * ·) (congrFun (omission_prod_singletons F ξ W) t).symm
    rw [hE, analyticOrderAt_mul (finiteHeckeOmissionMultiplier_analytic F ξ {v} z)
      (finiteHeckeOmissionMultiplier_analytic F ξ W z), finiteHeckeOmissionSingleton_order, ih]
    by_cases hz : P F ξ {v} z = 0
    · have hnot : v ∉ W.filter (fun v ↦ P F ξ {v} z = 0) :=
        fun h ↦ hv (Finset.mem_filter.mp h).1
      simp [Finset.filter_insert, hz, hnot, Nat.cast_add, add_comm]
    · simp [Finset.filter_insert, hz]

private theorem omissionSingleton_zero_line (v : Place F) (z : ℂ) (hz : P F ξ {v} z = 0) :
    z.re = 0 := by
  have he := euler_singleton_exp F ξ v z
  change P F ξ {v} z = 1 - heckeEulerCoefficient F ξ (chosenFiniteUniformizer F) v *
    Complex.exp (-(Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * z) at he
  rw [he, sub_eq_zero] at hz
  unfold heckeEulerCoefficient at hz
  split_ifs at hz with hv
  · have he := congrArg norm hz.symm
    rw [norm_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp, Real.exp_eq_one_iff] at he
    have hq : 0 < Real.log (v.asIdeal.absNorm : ℝ) := Real.log_pos
      (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr hq.ne')
  · simp at hz

theorem finiteHeckeOmissionMultiplier_zero_line (W : Finset (Place F)) (z : ℂ)
    (hz : P F ξ W z = 0) : z.re = 0 := by
  rw [omission_prod_singletons] at hz
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hz
  exact omissionSingleton_zero_line F ξ v z hv

/-- The trivial component has a common Euler zero at the origin for
every selected place, so its multiplicity there is the full cardinality. -/
theorem finiteHeckeOmissionMultiplier_trivial_order_zero (W : Finset (Place F)) :
    analyticOrderAt (finiteHeckeOmissionMultiplier F (normOneEulerCharacter F 1) W) 0 =
      (W.card : ℕ∞) := by
  have hχ (q : IdeleClass F) : normOneEulerCharacter F 1 q = 1 := by
    change (1 : PontryaginDual (K F)) ((ideleClassSplit F q).1) = 1
    rfl
  have hu (v : Place F) : unramifiedFiniteCharacter F (normOneEulerCharacter F 1) v :=
    fun u _ ↦ hχ _
  have hz (v : Place F) : finiteHeckeOmissionMultiplier F (normOneEulerCharacter F 1) {v} 0 = 0 := by
    unfold finiteHeckeOmissionMultiplier
    rw [Finset.prod_singleton]
    change 1 - heckeEulerCoefficient F (normOneEulerCharacter F 1) (chosenFiniteUniformizer F) v *
      (v.asIdeal.absNorm : ℂ) ^ (-(0 : ℂ)) = 0
    simp [heckeEulerCoefficient, hu v, hχ]
  rw [finiteHeckeOmissionMultiplier_order]
  simp [hz]

end Euler

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

private abbrev Pω := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω)
private abbrev G (r : GlobalBruhat F) := globalHeckeClearedZeta F ν ω r
private abbrev Z (r : GlobalBruhat F) := globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0

/-- The canonical pole-cleared orbital divisor. -/
def globalOrbitalGenerator (r : GlobalBruhat F) (W : Finset (Place F)) : ℂ → ℂ :=
  Pω F ω W * G F ν ω r

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The orbital divisor has precisely the selected Euler multiplicities
in addition to the original Hecke orders. -/
theorem globalOrbitalGenerator_order (r : GlobalBruhat F) (W : Finset (Place F)) (z : ℂ) :
    analyticOrderAt (globalOrbitalGenerator F ν ω r W) z =
      ((W.filter fun v ↦ Pω F ω {v} z = 0).card : ℕ∞) + analyticOrderAt (G F ν ω r) z := by
  rw [globalOrbitalGenerator, analyticOrderAt_mul
    (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z)
    (globalHeckeClearedZeta_analytic F ν ω r z), finiteHeckeOmissionMultiplier_order]

include μ hν in
/-- The orbital divisor has finite orders in the closed critical strip.
Its Schwartz–Bergman representative has exactly those orders. -/
theorem exists_globalOrbital_divisorData (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (W : Finset (Place F)) :
    let g := globalOrbitalGenerator F ν ω r W
    Differentiable ℂ g ∧
    (∀ z, analyticOrderAt g z ≠ ⊤) ∧
    (∀ z : ℂ, 0 < analyticOrderAt g z → z.re ∈ Icc (0 : ℝ) 1) ∧
    ∃ b : B, ∀ z, analyticOrderAt b.val z = analyticOrderAt g z := by
  intro g
  have hP (z : ℂ) := finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z
  have hG (z : ℂ) := globalHeckeClearedZeta_analytic F ν ω r z
  let b₀ := globalHeckeBergmanRepresentative F ν ω r
  let b := finiteHeckeOmissionBergmanMul F (normOneEulerCharacter F ω) W b₀
  have hb : b.val = Pω F ω W * b₀.val := funext
    (finiteHeckeOmissionBergmanMul_apply F (normOneEulerCharacter F ω) W b₀)
  refine ⟨fun z ↦ ((hP z).mul (hG z)).differentiableAt, ?_, ?_, b, fun z ↦ ?_⟩
  · intro z
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (globalHeckeClearedZeta_order_ne_top F ν ω r hr z)
    change analyticOrderAt (globalOrbitalGenerator F ν ω r W) z ≠ ⊤
    rw [globalOrbitalGenerator_order, ← hn, ← Nat.cast_add]
    exact ENat.natCast_ne_top _
  · intro z hz
    by_contra he
    have hout : z.re < 0 ∨ 1 < z.re := by simpa only [mem_Icc, not_and_or, not_le] using he
    have hp : Pω F ω W z ≠ 0 := by
      intro hp
      have hz₀ := finiteHeckeOmissionMultiplier_zero_line F (normOneEulerCharacter F ω) W z hp
      rw [hz₀] at hout
      norm_num at hout
    change 0 < analyticOrderAt (Pω F ω W * G F ν ω r) z at hz
    rw [analyticOrderAt_mul (hP z) (hG z), (hP z).analyticOrderAt_eq_zero.mpr hp,
      globalHeckeClearedZeta_order_zero_off_strip F ν η μ hν ω r hmin z hout, add_zero] at hz
    exact lt_irrefl _ hz
  · have hd : Differentiable ℂ b₀.val := by
      simpa only [preimage_univ, differentiableOn_univ] using b₀.property.2.1
    change analyticOrderAt b.val z = analyticOrderAt (Pω F ω W * G F ν ω r) z
    rw [hb, analyticOrderAt_mul (hP z) (hd.analyticAt z), analyticOrderAt_mul (hP z) (hG z),
      globalHeckeBergmanRepresentative_order]

#print axioms finiteHeckeOmissionMultiplier_order
#print axioms finiteHeckeOmissionMultiplier_trivial_order_zero
#print axioms finiteHeckeOmissionMultiplier_zero_line
#print axioms globalOrbitalGenerator_order
#print axioms exists_globalOrbital_divisorData

end

end Masullo
