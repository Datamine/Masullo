import ModulatedCyclicFourier
import BruhatWholeQuotientStages
import ElementarySchwartzSymbols
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter Function MeasureTheory Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 700000

section Compact

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

omit [T2Space G] [CompactSpace G] in
/-- A nontrivial character on the subgroup along which a test is constant
has zero Fourier coefficient. -/
theorem integral_character_eq_zero_of_invariant
    (χ : PontryaginDual G) (f : G → ℂ) (a : G)
    (hf : ∀ x, f (a * x) = f x) (ha : χ a ≠ 1) :
    (∫ x, f x * (χ x : ℂ) ∂μ) = 0 := by
  let J : ℂ := ∫ x, f x * (χ x : ℂ) ∂μ
  have hs := integral_mul_left_eq_self (μ := μ) (fun x : G ↦ f x * (χ x : ℂ)) a
  have he (x : G) : f (a * x) * (χ (a * x) : ℂ) =
      (χ a : ℂ) * (f x * (χ x : ℂ)) := by
    rw [hf, map_mul, Circle.coe_mul]
    ring
  have hJ : (χ a : ℂ) * J = J := by
    rw [← integral_const_mul]
    calc
      _ = ∫ x, f (a * x) * (χ (a * x) : ℂ) ∂μ := integral_congr_ae (.of_forall fun x ↦ (he x).symm)
      _ = J := hs
  have hz : ((χ a : ℂ) - 1) * J = 0 := by rw [sub_mul, one_mul, hJ, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left fun h ↦ ha (Subtype.ext (sub_eq_zero.mp h))

variable [LocallyCompactSpace G]

/-- Coefficients of a whole-group stage test are supported in the
annihilator of its structural kernel. -/
theorem compactBruhatFourierCoeff_eq_zero_off_stage_annihilator
    (P : WholeBruhatStage G) (u : P.val.Space) (χ : PontryaginDual G)
    (h : ∃ a ∈ P.val.1.kernel, χ a ≠ 1) :
    compactBruhatFourierCoeff μ χ (P.val.inclusion u) = 0 := by
  obtain ⟨a, ha, hχ⟩ := h
  have ha' : a ∈ P.coordinates.toMonoidHom.ker := P.coordinates_ker.symm ▸ ha
  have hPa : P.coordinates a = 1 := ha'
  have hp (x : G) : P.coordinates (a * x) = P.coordinates x :=
    (P.coordinates.map_mul a x).trans ((congrArg (· * P.coordinates x) hPa).trans (one_mul _))
  have hf (x : G) : (P.val.inclusion u).val (a * x) = (P.val.inclusion u).val x :=
    (P.realize_eq_coordinates u (a * x)).trans
      ((congrArg (fun z ↦ u.val z.toAdd) (hp x)).trans (P.realize_eq_coordinates u x).symm)
  rw [compactBruhatFourierCoeff_apply, integral_character_eq_zero_of_invariant μ χ _ a hf hχ,
    mul_zero]

omit [T2Space G] [LocallyCompactSpace G] in
/-- Differentiation along a compact-group one-parameter orbit acts on the
Fourier pairing by the negative character frequency. -/
theorem integral_character_orbitDerivative
    (c : Multiplicative ℝ →ₜ* G) (χ : PontryaginDual G) (freq : ℝ) (f D : G → ℂ)
    (hf : Continuous f) (hD : Continuous D)
    (hd : ∀ x, HasDerivAt (fun t : ℝ ↦ f (c (Multiplicative.ofAdd t) * x)) (D x) 0)
    (hχ : ∀ t : ℝ, (χ (c (Multiplicative.ofAdd t)) : ℂ) = Complex.exp ((freq * t : ℝ) * Complex.I)) :
    (∫ x, D x * (χ x : ℂ) ∂μ) =
      (-(freq : ℂ) * Complex.I) * (∫ x, f x * (χ x : ℂ) ∂μ) := by
  let J : ℂ := ∫ x, f x * (χ x : ℂ) ∂μ
  let g (t : ℝ) := c (Multiplicative.ofAdd t)
  let W (t : ℝ) (x : G) := f (g t * x) * (χ x : ℂ)
  let Z (t : ℝ) (x : G) := D (g t * x) * (χ x : ℂ)
  have hχc : Continuous (fun x : G ↦ (χ x : ℂ)) := continuous_subtype_val.comp χ.continuous
  have hW (t : ℝ) : Continuous (W t) := (hf.comp (continuous_const.mul continuous_id)).mul hχc
  have hZ (t : ℝ) : Continuous (Z t) := (hD.comp (continuous_const.mul continuous_id)).mul hχc
  have hdW (x : G) (t : ℝ) : HasDerivAt (fun s ↦ W s x) (Z t x) t := by
    have h := (hd (g t * x)).scomp_of_eq t ((hasDerivAt_id' t).sub_const t) (sub_self t).symm
    rw [one_smul] at h
    have he (s : ℝ) : g (s - t) * (g t * x) = g s * x := by
      rw [← mul_assoc]
      change (c (Multiplicative.ofAdd (s - t)) * c (Multiplicative.ofAdd t)) * x = _
      rw [← map_mul]
      exact congrArg (fun u : ℝ ↦ g u * x) (sub_add_cancel s t)
    have hshift : (fun s ↦ W s x) =
        fun s ↦ f (g (s - t) * (g t * x)) * (χ x : ℂ) := by
      funext s
      dsimp [W]
      rw [he]
    rw [hshift]
    exact h.mul_const (χ x : ℂ)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hD.continuousOn
  have hbound (t : ℝ) (x : G) : ‖Z t x‖ ≤ C := by
    rw [show Z t x = D (g t * x) * (χ x : ℂ) from rfl, norm_mul, Circle.norm_coe, mul_one]
    exact hC _ (mem_univ _)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := W) (F' := Z)
    (s := univ) (bound := fun _ : G ↦ C) univ_mem
    (.of_forall fun t ↦ (hW t).aestronglyMeasurable)
    ((hW 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hZ 0).aestronglyMeasurable (.of_forall fun x t _ ↦ hbound t x)
    (integrable_const _) (.of_forall fun x t _ ↦ hdW x t)).2
  have hg0 : g 0 = 1 := map_one c
  have he (t : ℝ) : (∫ x, W t x ∂μ) = Complex.exp ((-(freq : ℂ) * Complex.I) * (t : ℂ)) * J := by
    let F (x : G) := f x * (χ x : ℂ)
    have hp (x : G) : W t x = Complex.exp ((-(freq : ℂ) * Complex.I) * (t : ℂ)) * F (g t * x) := by
      have hprod : Complex.exp ((-(freq : ℂ) * Complex.I) * (t : ℂ)) * (χ (g t) : ℂ) = 1 := by
        rw [hχ t, ← Complex.exp_add]
        convert Complex.exp_zero using 2
        push_cast
        ring
      change f (g t * x) * (χ x : ℂ) =
        Complex.exp ((-(freq : ℂ) * Complex.I) * (t : ℂ)) *
          (f (g t * x) * (χ (g t * x) : ℂ))
      rw [map_mul, Circle.coe_mul]
      calc
        _ = f (g t * x) * (χ x : ℂ) * 1 := (mul_one _).symm
        _ = _ := by rw [← hprod]; ring
    calc
      _ = ∫ x, Complex.exp ((-(freq : ℂ) * Complex.I) * (t : ℂ)) * F (g t * x) ∂μ :=
        integral_congr_ae (.of_forall (hp))
      _ = _ := by rw [integral_const_mul, integral_mul_left_eq_self]
  have hd₀ := (((Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt.const_mul
    (-(freq : ℂ) * Complex.I)).cexp.mul_const J)
  have hd₁ : HasDerivAt (fun t : ℝ ↦ ∫ x, W t x ∂μ)
      ((-(freq : ℂ) * Complex.I) * J) 0 := by
    rw [funext he]
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_zero, Complex.ofReal_one,
      mul_zero, mul_one, Complex.exp_zero, one_mul] using hd₀
  simpa only [Z, hg0, one_mul] using h.unique hd₁

end Compact

section Elementary

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "E" => ElementarySchwartz m n r F

omit [DiscreteTopology F] [Finite F] in
/-- A compact elementary stage has no real vector or free discrete factor. -/
theorem elementaryLCAModel_compact_dimensions [CompactSpace (ElementaryLCAModel m n r F)] :
    m = 0 ∧ r = 0 := by
  constructor
  · by_contra hm
    let j : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    have hs : Surjective (fun x : A ↦ x.1 j) :=
      fun z ↦ ⟨(EuclideanSpace.single j z, 0, 0, 0), by simp⟩
    have hc : Continuous (fun x : A ↦ x.1 j) :=
      (PiLp.continuous_apply 2 _ j).comp continuous_fst
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) (hs.compactSpace hc)
  · by_contra hr
    let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hs : Surjective (fun x : A ↦ x.2.2.1 j) :=
      fun z ↦ ⟨(0, 0, fun _ ↦ z, 0), rfl⟩
    have hc : Continuous (fun x : A ↦ x.2.2.1 j) :=
      (continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℤ)) (hs.compactSpace hc)

variable [CompactSpace (Multiplicative (ElementaryLCAModel m n r F))]
  [MeasurableSpace (Multiplicative (ElementaryLCAModel m n r F))]
  [BorelSpace (Multiplicative (ElementaryLCAModel m n r F))]
  (μ : Measure (Multiplicative (ElementaryLCAModel m n r F))) [μ.IsHaarMeasure]

/-- Fourier pairing on an elementary stage, before normalization by Haar mass. -/
def elementaryFourierPairing (χ : PontryaginDual (Multiplicative A)) (f : E) : ℂ :=
  ∫ x : Multiplicative A, f.val x.toAdd * (χ x : ℂ) ∂μ

omit [BorelSpace (Multiplicative A)] in
/-- The uniform seminorm bounds every Fourier pairing with the same constant. -/
theorem norm_elementaryFourierPairing_le (χ : PontryaginDual (Multiplicative A)) (f : E) :
    ‖elementaryFourierPairing μ χ f‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f * μ.real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  rw [norm_mul, Circle.norm_coe, mul_one]
  change (‖f.val x.toAdd‖₊ : ENNReal).toReal ≤
    (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
  apply ENNReal.toReal_mono (f.property.2 _).ne
  rw [elementarySchwartzBound_zero]
  exact le_iSup (fun y ↦ (‖f.val y‖₊ : ENNReal)) x.toAdd

private theorem elementaryFourierPairing_derivative
    (v : X) (χ : PontryaginDual (Multiplicative A)) (L : X →L[ℝ] ℝ)
    (hL : ∀ u : X, χ (Multiplicative.ofAdd (elementaryCoverHom u)) = Circle.exp (L u))
    (f : E) :
    elementaryFourierPairing μ χ (elementarySchwartz_derivative (elementaryOneParameter v) f) =
      (-(L v : ℂ) * Complex.I) * elementaryFourierPairing μ χ f := by
  let c : Multiplicative ℝ →ₜ* Multiplicative A := elementaryOneParameter v
  let D : E := elementarySchwartz_derivative c f
  have hcont (g : E) : Continuous g.val :=
    elementary_continuous_of_fibres _ fun a b ↦ (g.property.1 a b).continuous
  have hd (x : Multiplicative A) :
      HasDerivAt (fun t : ℝ ↦ f.val (c (Multiplicative.ofAdd t) * x).toAdd) (D.val x.toAdd) 0 := by
    have hp := elementaryOrbit_hasDerivAt c f.val
      (fun a b ↦ (f.property.1 a b).differentiable (by simp)) x.toAdd
    have he : (fun t : ℝ ↦ f.val (c (Multiplicative.ofAdd t) * x).toAdd) =
        fun t : ℝ ↦ f.val (x.toAdd + (c (Multiplicative.ofAdd t)).toAdd) :=
      funext fun _ ↦ congrArg f.val (add_comm _ _)
    rw [he]
    exact hp
  have hχ (t : ℝ) : (χ (c (Multiplicative.ofAdd t)) : ℂ) = Complex.exp ((L v * t : ℝ) * Complex.I) := by
    change (χ (Multiplicative.ofAdd (elementaryCoverHom (t • v))) : ℂ) = _
    rw [hL, Circle.coe_exp, map_smul, smul_eq_mul, mul_comm t]
  letI : T2Space (Multiplicative A) :=
    T2Space.of_injective_continuous Multiplicative.toAdd.injective continuous_toAdd
  exact integral_character_orbitDerivative μ c χ (L v) _ _
    ((hcont f).comp continuous_toAdd) ((hcont D).comp continuous_toAdd) hd hχ

/-- Repeated invariant differentiation transfers arbitrary powers of a
character frequency to the Fourier pairing. -/
theorem elementaryFourierPairing_iterated_derivative
    (v : X) (χ : PontryaginDual (Multiplicative A)) (L : X →L[ℝ] ℝ)
    (hL : ∀ u : X, χ (Multiplicative.ofAdd (elementaryCoverHom u)) = Circle.exp (L u))
    (f : E) (k : ℕ) :
    elementaryFourierPairing μ χ ((elementarySchwartz_derivative (elementaryOneParameter v))^[k] f) =
      (-(L v : ℂ) * Complex.I) ^ k * elementaryFourierPairing μ χ f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', elementaryFourierPairing_derivative μ v χ L hL, ih, pow_succ]
    ring

/-- The compact-stage coefficient has polynomial decay of every order in each
one-parameter frequency, controlled by the corresponding differentiated test. -/
theorem elementaryFourierPairing_frequency_bound
    (v : X) (χ : PontryaginDual (Multiplicative A)) (L : X →L[ℝ] ℝ)
    (hL : ∀ u : X, χ (Multiplicative.ofAdd (elementaryCoverHom u)) = Circle.exp (L u))
    (f : E) (k : ℕ) :
    ‖L v‖ ^ k * ‖elementaryFourierPairing μ χ f‖ ≤
      elementarySchwartzSeminorm (0, 0, 0, 0)
        ((elementarySchwartz_derivative (elementaryOneParameter v))^[k] f) * μ.real univ := by
  have h := norm_elementaryFourierPairing_le μ χ
    ((elementarySchwartz_derivative (elementaryOneParameter v))^[k] f)
  rwa [elementaryFourierPairing_iterated_derivative μ v χ L hL, norm_mul, norm_pow,
    norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real] at h

end Elementary

section Stage

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (P : WholeBruhatStage G)

abbrev WholeBruhatStage.coordinateModel := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim
  P.val.2.latticeRank P.val.2.finiteFactor

local notation "A" => WholeBruhatStage.coordinateModel P

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The elementary coordinates of a whole-group stage of a compact group
have no Euclidean or free discrete factor. -/
theorem wholeBruhatStage_compact_dimensions :
    P.val.2.realDim = 0 ∧ P.val.2.latticeRank = 0 := by
  have hs : Surjective (fun x : G ↦ (P.coordinates x).toAdd) :=
    Multiplicative.toAdd.surjective.comp P.coordinates_surjective
  have hc : Continuous (fun x : G ↦ (P.coordinates x).toAdd) :=
    continuous_toAdd.comp P.coordinates.continuous
  letI : CompactSpace A := hs.compactSpace hc
  exact elementaryLCAModel_compact_dimensions (n := P.val.2.torusDim) (F := P.val.2.finiteFactor)

omit [T2Space G] [CompactSpace G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Pullback along the stage coordinates identifies elementary characters
with the characters annihilating the structural kernel. -/
theorem wholeBruhatStage_character_descends (χ : PontryaginDual G)
    (hχ : P.val.1.kernel ≤ χ.toMonoidHom.ker) :
    ∃! θ : PontryaginDual (Multiplicative A), θ.comp P.coordinates = χ := by
  let K := P.coordinates.toMonoidHom.ker
  have hk : K ≤ χ.toMonoidHom.ker := by
    dsimp only [K]
    rwa [P.coordinates_ker]
  let e : (G ⧸ K) ≃* Multiplicative A :=
    QuotientGroup.liftEquiv K P.coordinates_surjective rfl
  let d : Multiplicative A →* Circle := (QuotientGroup.lift K χ.toMonoidHom hk).comp e.symm.toMonoidHom
  have hd (x : G) : d (P.coordinates x) = χ x := by
    change QuotientGroup.lift K χ.toMonoidHom hk
      (e.symm (e (QuotientGroup.mk x))) = χ x
    rw [e.symm_apply_apply]
    rfl
  let θ : PontryaginDual (Multiplicative A) :=
    ⟨d, (P.coordinates_isOpenMap.isQuotientMap P.coordinates.continuous
      P.coordinates_surjective).continuous_iff.mpr
        (χ.continuous.congr fun x ↦ (hd x).symm)⟩
  refine ⟨θ, ?_, fun η hη ↦ ?_⟩
  · ext x
    exact congrArg (fun y : Circle ↦ (y : ℂ)) (hd x)
  · ext z
    obtain ⟨x, rfl⟩ := P.coordinates_surjective z
    exact (congrArg (fun ψ : PontryaginDual G ↦ (ψ x : ℂ)) hη).trans
      (congrArg (fun y : Circle ↦ (y : ℂ)) (hd x)).symm

variable [MeasurableSpace (Multiplicative (ElementaryLCAModel P.val.2.realDim P.val.2.torusDim
  P.val.2.latticeRank P.val.2.finiteFactor))]
  [BorelSpace (Multiplicative (ElementaryLCAModel P.val.2.realDim P.val.2.torusDim
    P.val.2.latticeRank P.val.2.finiteFactor))]

/-- On a compact stage, a surviving coefficient is the elementary Fourier
pairing for the pushforward Haar measure, divided by the original Haar mass. -/
theorem compactBruhatFourierCoeff_stage (μ : Measure G) [μ.IsHaarMeasure]
    (θ : PontryaginDual (Multiplicative A)) (u : P.val.Space) :
    compactBruhatFourierCoeff μ (θ.comp P.coordinates) (P.val.inclusion u) =
      (μ.real univ : ℂ)⁻¹ * elementaryFourierPairing (μ.map P.coordinates) θ u := by
  have hcont : Continuous (fun z : Multiplicative A ↦ u.val z.toAdd * (θ z : ℂ)) :=
    ((elementary_continuous_of_fibres _ fun a b ↦ (u.property.1 a b).continuous).comp
      continuous_toAdd).mul (continuous_subtype_val.comp θ.continuous)
  change (μ.real univ : ℂ)⁻¹ *
    (∫ x, (P.val.inclusion u).val x * (θ (P.coordinates x) : ℂ) ∂μ) =
    (μ.real univ : ℂ)⁻¹ *
      (∫ z, u.val z.toAdd * (θ z : ℂ) ∂(μ.map P.coordinates))
  apply congrArg ((μ.real univ : ℂ)⁻¹ * ·)
  have hmeas : AEMeasurable (P.coordinates : G → Multiplicative A) μ :=
    P.coordinates.continuous.measurable.aemeasurable
  refine (integral_congr_ae (.of_forall fun x ↦
    congrArg (· * (θ (P.coordinates x) : ℂ)) (P.realize_eq_coordinates u x))).trans ?_
  exact (integral_map hmeas hcont.aestronglyMeasurable).symm

end Stage

end

end Masullo
