import FourierCharacters
import OneParameterFlows
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Analysis.Complex.Circle

open Function Filter Set Topology

noncomputable section

namespace Masullo

abbrev CircleCharacter (G : Type*) [Monoid G] [TopologicalSpace G] := G →ₜ* Circle

/-- Each continuous circle character of the real line has a unique angular frequency. -/
theorem realCharacter_exp (χ : CircleCharacter (Multiplicative ℝ)) :
    ∃! c : ℝ, ∀ t : ℝ, (χ (Multiplicative.ofAdd t) : ℂ) =
      Complex.exp ((c : ℂ) * Complex.I * (t : ℂ)) := by
  let γ := Circle.toUnits.comp χ.toMonoidHom
  have hγ : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t) : ℂˣ) : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous_toFun.comp continuous_ofAdd)
  obtain ⟨c, hc, hu⟩ := complex_oneParameter_exp γ hγ
  have hn : Real.exp c.re = 1 := by
    have h := congrArg norm (hc 1)
    change ‖(χ (Multiplicative.ofAdd 1) : ℂ)‖ = ‖Complex.exp (c * (↑(1 : ℝ) : ℂ))‖ at h
    simpa only [Circle.norm_coe, Complex.ofReal_one, mul_one, Complex.norm_exp] using h.symm
  have hzero : c.re = 0 := Real.exp_injective (hn.trans Real.exp_zero.symm)
  have he : c = (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzero]
  refine ⟨c.im, fun t => ?_, fun a ha => ?_⟩
  · exact (hc t).trans (congrArg (fun z : ℂ => Complex.exp (z * (t : ℂ))) he)
  · have h := hu ((a : ℂ) * Complex.I) ha
    simpa [Complex.mul_im] using congrArg Complex.im h

private def realCharacterSlope (χ : CircleCharacter (Multiplicative ℝ)) : ℝ :=
  Classical.choose (realCharacter_exp χ)

private theorem realCharacterSlope_exp (χ : CircleCharacter (Multiplicative ℝ)) (t : ℝ) :
    (χ (Multiplicative.ofAdd t) : ℂ) =
      Complex.exp ((realCharacterSlope χ : ℂ) * Complex.I * (t : ℂ)) :=
  (Classical.choose_spec (realCharacter_exp χ)).1 t

private theorem realCharacterSlope_unique (χ : CircleCharacter (Multiplicative ℝ)) (c : ℝ)
    (hc : ∀ t : ℝ, (χ (Multiplicative.ofAdd t) : ℂ) =
      Complex.exp ((c : ℂ) * Complex.I * (t : ℂ))) : realCharacterSlope χ = c :=
  ((Classical.choose_spec (realCharacter_exp χ)).2 c hc).symm

private def realCharacterSlopeHom :
    CircleCharacter (Multiplicative ℝ) →* Multiplicative ℝ where
  toFun χ := Multiplicative.ofAdd (realCharacterSlope χ)
  map_one' := realCharacterSlope_unique 1 0 (by simp)
  map_mul' χ ψ := by
    apply realCharacterSlope_unique
    intro t
    change (χ (Multiplicative.ofAdd t) : ℂ) * (ψ (Multiplicative.ofAdd t) : ℂ) =
      Complex.exp (((realCharacterSlope χ + realCharacterSlope ψ : ℝ) : ℂ) * Complex.I * (t : ℂ))
    rw [realCharacterSlope_exp, realCharacterSlope_exp, ← Complex.exp_add, Complex.ofReal_add]
    congr 1
    ring

private theorem realCharacterSlope_continuous : Continuous realCharacterSlope := by
  have hc : Continuous realCharacterSlopeHom := by
    apply continuous_of_continuousAt_one
    have hconv : Tendsto Multiplicative.ofAdd (𝓝 (0 : ℝ)) (𝓝 (1 : Multiplicative ℝ)) :=
      continuous_ofAdd.continuousAt
    rw [ContinuousAt, map_one]
    change Tendsto (Multiplicative.ofAdd ∘ realCharacterSlope) (𝓝 1) (𝓝 1)
    apply hconv.comp
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let K := Multiplicative.ofAdd '' Icc (-(Real.pi / ε)) (Real.pi / ε)
    let U : Set Circle := {z | 0 < (z : ℂ).re}
    have hK : IsCompact K := isCompact_Icc.image continuous_ofAdd
    have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
    have hN : ∀ᶠ χ : CircleCharacter (Multiplicative ℝ) in 𝓝 1, MapsTo χ K U := by
      apply ((ContinuousMap.isOpen_setOfPred_mapsTo hK hU).preimage
        (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous).mem_nhds
      exact fun _ _ => by simp [U]
    filter_upwards [hN] with χ hχ
    rw [Real.dist_eq, sub_zero]
    by_contra! h
    let a := realCharacterSlope χ
    have ha : a ≠ 0 := by
      intro hz
      have : ε ≤ |a| := h
      simp [hz, not_le.mpr hε] at this
    let t := Real.pi / a
    have ht : |t| ≤ Real.pi / ε := by
      rw [abs_div, abs_of_pos Real.pi_pos]
      exact div_le_div_of_nonneg_left Real.pi_pos.le hε h
    have htK : Multiplicative.ofAdd t ∈ K := ⟨t, abs_le.mp ht, rfl⟩
    have hval := hχ htK
    change 0 < (χ (Multiplicative.ofAdd t) : ℂ).re at hval
    rw [realCharacterSlope_exp] at hval
    have hangle : (a : ℂ) * Complex.I * (t : ℂ) = (Real.pi : ℂ) * Complex.I := by
      calc
        _ = ((a * t : ℝ) : ℂ) * Complex.I := by rw [Complex.ofReal_mul]; ring
        _ = _ := by congr 2; exact mul_div_cancel₀ Real.pi ha
    change 0 < (Complex.exp ((a : ℂ) * Complex.I * (t : ℂ))).re at hval
    rw [hangle, Complex.exp_pi_mul_I] at hval
    norm_num at hval
  exact continuous_toAdd.comp hc

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

private def restrictCharacter (a : Multiplicative ℝ →ₜ* G) :
    CircleCharacter G →* CircleCharacter (Multiplicative ℝ) where
  toFun χ := χ.comp a
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The real slope in the exponential along the supplied one-parameter subgroup. -/
def characterSlope (a : Multiplicative ℝ →ₜ* G) : CircleCharacter G →* Multiplicative ℝ :=
  realCharacterSlopeHom.comp (restrictCharacter a)

theorem characterSlope_continuous (a : Multiplicative ℝ →ₜ* G) :
    Continuous (characterSlope a) :=
  (continuous_ofAdd.comp realCharacterSlope_continuous).comp
    (ContinuousMonoidHom.continuous_comp_left a)

/-- Exponential form of a character on a real one-parameter subgroup. -/
theorem characterSlope_eq_exp (a : Multiplicative ℝ →ₜ* G) (χ : CircleCharacter G) (t : ℝ) :
    χ (a (Multiplicative.ofAdd t)) =
      Circle.exp (Multiplicative.toAdd (characterSlope a χ) * t) := by
  apply Circle.ext
  rw [Circle.coe_exp]
  have h := realCharacterSlope_exp (χ.comp a) t
  change (χ (a (Multiplicative.ofAdd t)) : ℂ) =
    Complex.exp (((Multiplicative.toAdd (characterSlope a χ) : ℝ) : ℂ) * Complex.I * (t : ℂ)) at h
  rw [h, Complex.ofReal_mul]
  congr 1
  ring

/-- The exponential form determines its real slope uniquely. -/
theorem characterSlope_unique (a : Multiplicative ℝ →ₜ* G) (χ : CircleCharacter G) (c : ℝ)
    (h : ∀ t : ℝ, χ (a (Multiplicative.ofAdd t)) = Circle.exp (c * t)) :
    Multiplicative.toAdd (characterSlope a χ) = c := by
  apply realCharacterSlope_unique
  intro t
  change (χ (a (Multiplicative.ofAdd t)) : ℂ) = Complex.exp ((c : ℂ) * Complex.I * (t : ℂ))
  have hh := congrArg ((↑) : Circle → ℂ) (h t)
  rw [Circle.coe_exp, Complex.ofReal_mul] at hh
  rw [hh]
  congr 1
  ring

private theorem characterSlope_compact_trivial (a : Multiplicative ℝ →ₜ* G)
    (K : Subgroup (CircleCharacter G)) (hK : IsCompact (K : Set (CircleCharacter G)))
    (χ : K) : characterSlope a χ = 1 := by
  let c := Multiplicative.toAdd ∘ characterSlope a
  have hc : IsCompact (c '' (K : Set (CircleCharacter G))) :=
    hK.image (continuous_toAdd.comp (characterSlope_continuous a))
  obtain ⟨b, hb⟩ := hc.bddAbove
  have hbound (n : ℕ) : (n : ℝ) * |c χ| ≤ b := by
    by_cases hp : 0 ≤ c χ
    · rw [abs_of_nonneg hp]
      have h := hb (mem_image_of_mem c (K.pow_mem χ.property n))
      simpa [c, map_pow, nsmul_eq_mul] using h
    · rw [abs_of_neg (lt_of_not_ge hp)]
      have h := hb (mem_image_of_mem c (K.pow_mem (K.inv_mem χ.property) n))
      simpa [c, map_pow, map_inv, nsmul_eq_mul] using h
  change c χ = 0
  by_contra hne
  obtain ⟨n, hn⟩ := exists_nat_gt (b / |c χ|)
  exact (not_lt_of_ge (hbound n)) ((div_lt_iff₀ (abs_pos.mpr hne)).mp hn)

def directionalDeriv (a : Multiplicative ℝ →ₜ* G) (f : G → ℂ) (g : G) : ℂ :=
  deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0

private theorem hasDerivAt_character (a : Multiplicative ℝ →ₜ* G) (χ : CircleCharacter G)
    (g : G) (c : ℂ) :
    HasDerivAt (fun t : ℝ => c * (χ (g * a (Multiplicative.ofAdd t)) : ℂ))
      (c * (((Multiplicative.toAdd (characterSlope a χ) : ℝ) : ℂ) * Complex.I) * χ g) 0 := by
  let k := ((Multiplicative.toAdd (characterSlope a χ) : ℝ) : ℂ) * Complex.I
  have hfun : (fun t : ℝ => c * (χ (g * a (Multiplicative.ofAdd t)) : ℂ)) =
      fun t : ℝ => (c * χ g) * Complex.exp (k * (t : ℂ)) := by
    funext t
    rw [map_mul, Circle.coe_mul, mul_assoc]
    congr 2
    change ((χ.comp a) (Multiplicative.ofAdd t) : ℂ) =
      Complex.exp ((realCharacterSlope (χ.comp a) : ℂ) * Complex.I * (t : ℂ))
    exact realCharacterSlope_exp (χ.comp a) t
  have hz : HasDerivAt (fun z : ℂ => Complex.exp (k * z)) k 0 := by
    simpa using ((hasDerivAt_id' (0 : ℂ)).const_mul k).cexp
  rw [hfun]
  simpa only [k, mul_left_comm, mul_comm, mul_assoc] using hz.comp_ofReal.const_mul (c * χ g)

/-- Lemma D.1.6.13. Each character is a joint eigenfunction of all directional
derivatives, with the product symbol invariant under compact subgroups of the dual. -/
theorem directionalDeriv_character_symbol (A : List (Multiplicative ℝ →ₜ* G))
    (χ : CircleCharacter G) :
    let symbol (ψ : CircleCharacter G) :=
      (A.map fun a => ((Multiplicative.toAdd (characterSlope a ψ) : ℝ) : ℂ) * Complex.I).prod
    (∀ g, (A.foldr directionalDeriv (fun x => (χ x : ℂ))) g = symbol χ * χ g) ∧
    (A.foldr directionalDeriv (fun x => (χ x : ℂ))) 1 = symbol χ ∧
    ∀ (K : Subgroup (CircleCharacter G)), IsCompact (K : Set (CircleCharacter G)) →
      ∀ ψ : K, symbol (χ * ψ) = symbol χ := by
  dsimp only
  have hf : ∀ g : G, (A.foldr directionalDeriv (fun x => (χ x : ℂ))) g =
      (A.map fun a => ((Multiplicative.toAdd (characterSlope a χ) : ℝ) : ℂ) * Complex.I).prod * χ g := by
    induction A with
    | nil => simp
    | cons a A ih =>
      intro g
      rw [List.foldr_cons, show (A.foldr directionalDeriv (fun x => (χ x : ℂ))) =
        fun g => (A.map fun a => ((Multiplicative.toAdd (characterSlope a χ) : ℝ) : ℂ) * Complex.I).prod *
          χ g from funext ih]
      rw [directionalDeriv, (hasDerivAt_character a χ g _).deriv, List.map_cons, List.prod_cons,
        mul_comm ((A.map _).prod)]
  refine ⟨hf, by simpa using hf 1, fun K hK ψ => ?_⟩
  have hm (a : Multiplicative ℝ →ₜ* G) : characterSlope a (χ * ψ) = characterSlope a χ := by
    rw [map_mul, characterSlope_compact_trivial a K hK ψ, mul_one]
  simp only [hm]

/-- The compact-subgroup invariance extends to every finite complex linear
combination of words in directional derivatives, including the empty word. -/
theorem directionalDeriv_polynomial_symbol_invariant
    (D : List (ℂ × List (Multiplicative ℝ →ₜ* G))) (χ : CircleCharacter G)
    (K : Subgroup (CircleCharacter G)) (hK : IsCompact (K : Set (CircleCharacter G))) (ψ : K) :
    let p (θ : CircleCharacter G) := (D.map fun (c, A) =>
      c * (A.foldr directionalDeriv (fun x => (θ x : ℂ))) 1).sum
    p (χ * ψ) = p χ := by
  dsimp only
  have h (A : List (Multiplicative ℝ →ₜ* G)) :
      (A.foldr directionalDeriv (fun x => ((χ * ψ : CircleCharacter G) x : ℂ))) 1 =
        (A.foldr directionalDeriv (fun x => (χ x : ℂ))) 1 := by
    rw [(directionalDeriv_character_symbol A (χ * ψ)).2.1,
      (directionalDeriv_character_symbol A χ).2.1]
    exact (directionalDeriv_character_symbol A χ).2.2 K hK ψ
  simp only [h]

end Masullo
