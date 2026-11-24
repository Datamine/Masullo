import CyclicMellinMoments
import ModulatedCyclicComparison
import ModulatedJumpPoisson

open Function MeasureTheory Set

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 8

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
variable (ρ : Measure m.toMonoidHom.ker) [IsFiniteMeasure ρ]

local notation "X" => PositiveRealExponentialDecay (univ : Set ℝ)

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
include hτ in
/-- The log-coordinate moment of a radial profile equals its actual
group integral, with the mass of the compact kernel Haar retained. -/
theorem modulatedLogMeasure_radial_moment
    (χ : CircleCharacter G) (r : ℝ → ℂ) (f : G → ℂ)
    (hf : ∀ g, f g = r (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ))
    (t : ℝ) (k : ℕ) :
    ∫ g, f g * ((χ * modulusCharacter m t) g : ℂ) * ((m g).toAdd : ℂ) ^ k
        ∂modulatedLogMeasure m τ hτ ρ =
      (ρ.real univ : ℂ) *
        ∫ x : ℝ, Complex.exp (((t : ℂ) * Complex.I) * (x : ℂ)) * ((x : ℂ) ^ k * r x) := by
  let K := m.toMonoidHom.ker
  let e := (modulatedLogSplit m τ hτ).toMeasurableEquiv
  let F (x : ℝ) : ℂ := Complex.exp (((t : ℂ) * Complex.I) * (x : ℂ)) * ((x : ℂ) ^ k * r x)
  change (∫ g, f g * ((χ * modulusCharacter m t) g : ℂ) * ((m g).toAdd : ℂ) ^ k
       ∂Measure.map e (volume.prod ρ)) = _
  rw [integral_map_equiv]
  have hval (p : ℝ × K) :
      f (e p) * ((χ * modulusCharacter m t) (e p) : ℂ) * ((m (e p)).toAdd : ℂ) ^ k =
        F p.1 * (1 : ℂ) := by
    have hp : (m (e p)).toAdd = p.1 := by
      change (m (τ (Multiplicative.ofAdd p.1) * p.2.val)).toAdd = p.1
      rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one, toAdd_ofAdd]
    have hc : ((χ * modulusCharacter m t) (e p) : ℂ) =
        (χ (e p) : ℂ) * Complex.exp (((t : ℂ) * Complex.I) * (p.1 : ℂ)) := by
      change ((χ (e p) * Circle.exp (t * (m (e p)).toAdd) : Circle) : ℂ) = _
      rw [Circle.coe_mul, hp]
      congr 1
      change Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) = _
      rw [Complex.ofReal_mul]
      ring_nf
    have hi : (((χ (e p))⁻¹ : Circle) : ℂ) * (χ (e p) : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    rw [hf, hc, hp]
    calc
      _ = r p.1 * ((((χ (e p))⁻¹ : Circle) : ℂ) * (χ (e p) : ℂ)) *
           (Complex.exp (((t : ℂ) * Complex.I) * (p.1 : ℂ)) * (p.1 : ℂ) ^ k) := by ring
      _ = _ := by rw [hi, mul_one]; dsimp [F]; ring
  calc
    _ = ∫ p : ℝ × K, F p.1 * (1 : ℂ) ∂volume.prod ρ :=
      integral_congr_ae (.of_forall hval)
    _ = (∫ x : ℝ, F x) * ∫ _ : K, (1 : ℂ) ∂ρ :=
      integral_prod_mul (μ := volume) (ν := ρ) F (fun _ : K ↦ 1)
    _ = _ := by rw [integral_const, Complex.real_smul, mul_one, mul_comm]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem cyclicMellinFactor_eq_zero_iff_character (χ : CircleCharacter G)
    (t : ℝ) (g : G) :
    cyclicMellinFactor ((m g).toAdd, (χ g)⁻¹) ((t : ℂ) * Complex.I) = 0 ↔
      (χ * modulusCharacter m t) g = 1 := by
  let x := (m g).toAdd
  let z := Circle.exp (t * x)
  have hz : Complex.exp (-((x : ℂ) * ((t : ℂ) * Complex.I))) = (z : ℂ)⁻¹ := by
    rw [Complex.exp_neg]
    congr 1
    change Complex.exp ((x : ℂ) * ((t : ℂ) * Complex.I)) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
    rw [Complex.ofReal_mul]
    ring_nf
  change 1 - (((χ g)⁻¹ : Circle) : ℂ) *
    Complex.exp (-((x : ℂ) * ((t : ℂ) * Complex.I))) = 0 ↔ χ g * z = 1
  rw [hz, Circle.coe_inv, ← mul_inv_rev, mul_comm (z : ℂ) (χ g : ℂ), ← Circle.coe_mul, ← Circle.coe_inv]
  constructor
  · intro h
    have hi : (χ g * z)⁻¹ = 1 :=
      Subtype.ext ((sub_eq_zero.mp h).symm.trans Circle.coe_one.symm)
    exact inv_eq_one.mp hi
  · rintro h
    rw [h, inv_one, Circle.coe_one, sub_self]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
open Classical in
/-- The Mellin zero order at this frequency is the manuscript's count of
generators on which the sampled character is trivial. -/
theorem modulated_cyclicMellinMultiplicity (χ : CircleCharacter G) (gs : List G) (t : ℝ) :
    cyclicMellinMultiplicity (gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹))
        ((t : ℂ) * Complex.I) =
      gs.countP (fun g ↦ decide ((χ * modulusCharacter m t) g = 1)) := by
  simp only [cyclicMellinMultiplicity, List.countP_map, Function.comp_def,
    cyclicMellinFactor_eq_zero_iff_character]

include hτ in
/-- The group-integral moments in (4.6.1.14) give continuous functionals
on the actual finite-difference isotype quotient. -/
theorem exists_modulatedCyclicMellinMoment_quotient
    (hm : IsProperMap m) (w : PontryaginDual m.toMonoidHom.ker)
    (gs : List G) (hgs : ∀ g ∈ gs, 0 < (m g).toAdd)
    (t : ℝ) (k : ℕ)
    (hk : k < cyclicMellinMultiplicity
      (gs.map fun g ↦ ((m g).toAdd, (extendModulatedCharacter m τ hτ w g)⁻¹))
      ((t : ℂ) * Complex.I)) :
    let H := modulatedDecayIsotype m w univ
    let P := (modulatedDecayIsotypeDifferenceProduct m τ hτ w hm univ univ_nonempty gs).range
    let ξ := extendModulatedCharacter m τ hτ w * modulusCharacter m t
    ∃ L : (H ⧸ P) →L[ℂ] ℂ, ∀ f : H,
      L (P.mkQ f) = ∫ g, f.val.val g * (ξ g : ℂ) * ((m g).toAdd : ℂ) ^ k
        ∂modulatedLogMeasure m τ hτ ρ := by
  dsimp only
  let H := modulatedDecayIsotype m w univ
  let χ := extendModulatedCharacter m τ hτ w
  let P := (modulatedDecayIsotypeDifferenceProduct m τ hτ w hm univ univ_nonempty gs).range
  let ys := gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹)
  let V := (logDecayCyclicDifferenceProduct univ univ_nonempty ys).range
  have hys : ∀ y ∈ ys, 0 < y.1 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    exact hgs g hg
  obtain ⟨e, q, eInv, hq⟩ := exists_modulatedDecayRadialDifferenceQuotient
    m τ hτ w hm univ univ_nonempty gs
  obtain ⟨e₀, hv₀, hi₀, _⟩ := exists_modulatedDecayRadialDifferenceModel m τ hτ w hm univ univ_nonempty
  have he (r : X) : e r = e₀ r := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    funext x
    exact ((eInv (e₀ r) x).trans ((hi₀ (e₀ r) x).symm.trans
      (congrArg (fun f : X ↦ f.val x) (e₀.symm_apply_apply r)))).symm
  obtain ⟨J, hJ⟩ := exists_cyclicMellinMoment_quotient ys hys ((t : ℂ) * Complex.I) k hk
  let L : (H ⧸ P) →L[ℂ] ℂ := (ρ.real univ : ℂ) • (J.comp q.symm.toContinuousLinearMap)
  refine ⟨L, fun f ↦ ?_⟩
  obtain ⟨r, rfl⟩ := e.surjective f
  have hr (g : G) : (e r).val.val g = r.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ) :=
    (congrArg (fun f : H ↦ f.val.val g) (he r)).trans (hv₀ r g)
  change (ρ.real univ : ℂ) * J (q.symm (P.mkQ (e r))) = _
  rw [← hq r, q.symm_apply_apply, hJ]
  exact (modulatedLogMeasure_radial_moment m τ hτ ρ χ r.val (e r).val.val hr t k).symm

include hτ in
/-- The actual Haar moments along each integer-spaced phase fibre are
Schwartz sequences. Restriction to any prescribed multiplicities keeps
the same weighted bounds. -/
theorem modulatedCyclicMellinMoments_sampled_rapid
    (hm : IsProperMap m) (w : PontryaginDual m.toMonoidHom.ker)
    (f : modulatedDecayIsotype m w univ) (a d : ℝ) (hd : d ≠ 0) (k N : ℕ) :
    let χ := extendModulatedCharacter m τ hτ w
    ∃ C : ℝ, ∀ n : ℤ, |(n : ℝ)| ^ N *
      ‖∫ g, f.val.val g * ((χ * modulusCharacter m (a + d * (n : ℝ))) g : ℂ) *
        ((m g).toAdd : ℂ) ^ k ∂modulatedLogMeasure m τ hτ ρ‖ ≤ C := by
  dsimp only
  let χ := extendModulatedCharacter m τ hτ w
  obtain ⟨e, he, _, _⟩ := exists_modulatedDecayRadialDifferenceModel m τ hτ w hm univ univ_nonempty
  obtain ⟨r, rfl⟩ := e.surjective f
  obtain ⟨C, hC⟩ := entireLogMellin_sampledJets_rapid r a d hd k N
  let b : ℂ := ρ.real univ
  refine ⟨‖b‖ * C, fun n ↦ ?_⟩
  let t := a + d * (n : ℝ)
  let z := (t : ℂ) * Complex.I
  have hMoment : (∫ g, (e r).val.val g * ((χ * modulusCharacter m t) g : ℂ) *
        ((m g).toAdd : ℂ) ^ k ∂modulatedLogMeasure m τ hτ ρ) =
      b * iteratedDeriv k (entireLogMellin r).val z :=
    (modulatedLogMeasure_radial_moment m τ hτ ρ χ r.val (e r).val.val (he r) t k).trans
      (congrArg (b * ·) (entireLogMellin_iteratedDeriv_eq_moment r z k).symm)
  change |(n : ℝ)| ^ N * ‖∫ g, (e r).val.val g * ((χ * modulusCharacter m t) g : ℂ) *
      ((m g).toAdd : ℂ) ^ k ∂modulatedLogMeasure m τ hτ ρ‖ ≤ _
  rw [hMoment, norm_mul, mul_left_comm (|(n : ℝ)| ^ N)]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)

include hτ in
/-- Rapid decay in the integer coordinate of each actual cyclic
annihilator fibre, using its normalized phase representative. -/
theorem modulatedCyclicMellinMoments_fibre_rapid
    (hm : IsProperMap m) (w : PontryaginDual m.toMonoidHom.ker)
    (f : modulatedDecayIsotype m w univ) (γ : G) (hγ : 0 < (m γ).toAdd) (k N : ℕ) :
    let χ := extendModulatedCharacter m τ hτ w
    ∃ C : ℝ, ∀ n : ℤ, |(n : ℝ)| ^ N *
      ‖∫ g, f.val.val g * (modulatedCyclicCharacter m γ hγ χ n (QuotientGroup.mk g) : ℂ) *
        ((m g).toAdd : ℂ) ^ k ∂modulatedLogMeasure m τ hτ ρ‖ ≤ C := by
  dsimp only
  let χ := extendModulatedCharacter m τ hτ w
  let d := 2 * Real.pi / (m γ).toAdd
  obtain ⟨a, ha⟩ := modulatedCyclicCharacter_affine m γ hγ χ
  have hd : d ≠ 0 := (div_pos Real.two_pi_pos hγ).ne'
  obtain ⟨C, hC⟩ := modulatedCyclicMellinMoments_sampled_rapid
    m τ hτ ρ hm w f a d hd k N
  refine ⟨C, fun n ↦ ?_⟩
  convert hC n using 3
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g ↦
    congrArg (fun z : Circle ↦ f.val.val g * (z : ℂ) * ((m g).toAdd : ℂ) ^ k) (ha n g)

include hτ in
open Classical in
/-- The common kernel of the Haar moments is the actual finite-difference
range on the norm-one isotype. The number of moments at a character is
the number of generators on which that character is trivial. -/
theorem modulatedCyclicMellinMoments_ker_eq_range [ρ.IsHaarMeasure]
    (hm : IsProperMap m) (w : PontryaginDual m.toMonoidHom.ker)
    (gs : List G) (hgs : ∀ g ∈ gs, 0 < (m g).toAdd)
    (f : modulatedDecayIsotype m w univ) :
    let χ := extendModulatedCharacter m τ hτ w
    f ∈ (modulatedDecayIsotypeDifferenceProduct m τ hτ w hm univ univ_nonempty gs).range ↔
      ∀ t : ℝ, ∀ k < gs.countP (fun g ↦ decide ((χ * modulusCharacter m t) g = 1)),
        (∫ g, f.val.val g * ((χ * modulusCharacter m t) g : ℂ) * ((m g).toAdd : ℂ) ^ k
          ∂modulatedLogMeasure m τ hτ ρ) = 0 := by
  dsimp only
  let H := modulatedDecayIsotype m w univ
  let χ := extendModulatedCharacter m τ hτ w
  let ys := gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹)
  let D := logDecayCyclicDifferenceProduct univ univ_nonempty ys
  let A := modulatedDecayIsotypeDifferenceProduct m τ hτ w hm univ univ_nonempty gs
  have hys : ∀ y ∈ ys, 0 < y.1 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    exact hgs g hg
  obtain ⟨e, he, _, hA⟩ := exists_modulatedDecayRadialDifferenceModel m τ hτ w hm univ univ_nonempty
  obtain ⟨r, rfl⟩ := e.surjective f
  have hrange : e r ∈ A.range ↔ r ∈ D.range := by
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨u, rfl⟩ := e.surjective v
      exact ⟨u, e.injective ((hA gs u).symm.trans hv)⟩
    · rintro ⟨u, hu⟩
      exact ⟨e u, (hA gs u).trans (congrArg e hu)⟩
  let b : ℂ := ρ.real univ
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  have hMoment (t : ℝ) (k : ℕ) :
      (∫ g, (e r).val.val g * ((χ * modulusCharacter m t) g : ℂ) *
        ((m g).toAdd : ℂ) ^ k ∂modulatedLogMeasure m τ hτ ρ) =
      b * iteratedDeriv k (entireLogMellin r).val ((t : ℂ) * Complex.I) :=
    (modulatedLogMeasure_radial_moment m τ hτ ρ χ r.val (e r).val.val (he r) t k).trans
      (congrArg (b * ·) (entireLogMellin_iteratedDeriv_eq_moment r _ k).symm)
  have hcount (t : ℝ) : cyclicMellinMultiplicity ys ((t : ℂ) * Complex.I) =
      gs.countP (fun g ↦ decide ((χ * modulusCharacter m t) g = 1)) :=
    modulated_cyclicMellinMultiplicity m χ gs t
  change e r ∈ A.range ↔ _
  rw [hrange, logDecayCyclicDifferenceProduct_mem_range_iff_mellinJets ys hys r]
  constructor
  · intro hf t k hk
    rw [hMoment, hf _ k ((hcount t).symm ▸ hk), mul_zero]
  · intro hf z k hk
    have hz := cyclicMellinMultiplicity_re_eq_zero ys hys z ((Nat.zero_le k).trans_lt hk)
    have hz' : ((z.im : ℂ) * Complex.I) = z := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hz]
    have hk' : k < gs.countP (fun g ↦ decide ((χ * modulusCharacter m z.im) g = 1)) :=
      hcount z.im ▸ (hz'.symm ▸ hk)
    have hh := hf z.im k hk'
    rw [hMoment, hz'] at hh
    exact (mul_eq_zero.mp hh).resolve_left hb

end

end Masullo
