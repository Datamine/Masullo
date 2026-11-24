import FourierSymbols
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Complex Function Set Topology

namespace Masullo

noncomputable section

private theorem circle_eq_one_of_re_eq_one (z : Circle) (hz : (z : ℂ).re = 1) : z = 1 := by
  have hn := Circle.normSq_coe z
  rw [normSq_apply, hz] at hn
  have hi : (z : ℂ).im = 0 := by nlinarith [sq_nonneg (z : ℂ).im]
  apply Circle.ext
  exact Complex.ext (by simpa using hz) (by simpa using hi)

private theorem circle_subgroup_trivial_in_right_halfPlane (H : Subgroup Circle)
    (hH : ∀ z ∈ H, 0 < (z : ℂ).re) : H = ⊥ := by
  let K := H.topologicalClosure
  have hc : IsCompact (K : Set Circle) := H.isClosed_topologicalClosure.isCompact
  have hre : Continuous (fun z : Circle => (z : ℂ).re) :=
    Complex.continuous_re.comp continuous_subtype_val
  have hnonneg (z : Circle) (hz : z ∈ K) : 0 ≤ (z : ℂ).re := by
    have hs : (H : Set Circle) ⊆ {z | 0 ≤ (z : ℂ).re} := fun z hz => (hH z hz).le
    exact closure_minimal hs (isClosed_le continuous_const hre) hz
  obtain ⟨w, hw, hmin⟩ := hc.exists_isMinOn ⟨1, K.one_mem⟩ hre.continuousOn
  apply le_antisymm _ bot_le
  intro z hz
  change z = 1
  by_contra hz'
  have hlt : (z : ℂ).re < 1 := by
    have hr := re_le_norm (z : ℂ)
    rw [Circle.norm_coe] at hr
    exact lt_of_le_of_ne hr (fun h => hz' (circle_eq_one_of_re_eq_one z h))
  have hwlt : (w : ℂ).re < 1 := (hmin (H.le_topologicalClosure hz)).trans_lt hlt
  have hw₀ := hnonneg w hw
  have hs := hmin (K.mul_mem hw hw)
  change (w : ℂ).re ≤ ((w * w : Circle) : ℂ).re at hs
  rw [Circle.coe_mul, mul_re] at hs
  have hn := Circle.normSq_coe w
  rw [normSq_apply] at hn
  nlinarith [mul_pos (sub_pos.mpr hwlt) (show 0 < 2 * (w : ℂ).re + 1 by linarith)]

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Characters trivial on all integral powers of a fixed element. -/
abbrev MonogenicAnnihilator (γ : G) : Subgroup (CircleCharacter G) :=
  (show CircleCharacter G →* Circle from
    { toFun := fun χ => χ γ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }).ker

omit [IsTopologicalGroup G] in
theorem mem_monogenicAnnihilator_iff (χ : CircleCharacter G) (γ : G) :
    χ ∈ MonogenicAnnihilator γ ↔ ∀ n : ℤ, χ (γ ^ n) = 1 := by
  constructor
  · intro h n
    have hγ : χ γ = 1 := h
    rw [map_zpow, hγ, one_zpow]
  · intro h
    change χ γ = 1
    simpa using h 1

omit [IsTopologicalGroup G] in
private theorem modulated_compact_representatives
    (μ : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ))
    (hproper : IsProperMap μ) :
    ∃ K : Set G, IsCompact K ∧ ∀ g : G, ∃ n : ℤ, g / γ ^ n ∈ K := by
  let ℓ := Multiplicative.toAdd (μ γ)
  let K := μ ⁻¹' (Multiplicative.ofAdd '' Icc (0 : ℝ) ℓ)
  have hc : IsCompact K := hproper.isCompact_preimage
    (isCompact_Icc.image continuous_ofAdd)
  refine ⟨K, hc, fun g => ?_⟩
  let y := Multiplicative.toAdd (μ g)
  let n := toIcoDiv hγ 0 y
  refine ⟨n, ⟨toIcoMod hγ 0 y, ?_, ?_⟩⟩
  · have h := toIcoMod_mem_Ico' hγ y
    exact ⟨h.1, h.2.le⟩
  · apply Multiplicative.toAdd.injective
    simpa only [map_div, map_zpow, toAdd_div, toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul] using
      (self_sub_toIcoDiv_mul hγ 0 y).symm

omit [IsTopologicalGroup G] in
/-- The cyclic quotient in Lemma 4.4.2.5 is compact. Adapted from the
Apache-2.0 RiemannMasullo proof at a735545. -/
theorem modulatedCyclicQuotient_compact (μ : G →ₜ* Multiplicative ℝ)
    (hproper : IsProperMap μ) (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ)) :
    CompactSpace (G ⧸ Subgroup.zpowers γ) := by
  obtain ⟨K, hK, hrep⟩ := modulated_compact_representatives μ γ hγ hproper
  have hsurj : (QuotientGroup.mk : G → G ⧸ Subgroup.zpowers γ) '' K = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn⟩ := hrep g
    refine ⟨g / γ ^ n, hn, ?_⟩
    rw [QuotientGroup.mk_div,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers γ n), div_one]
  rw [← isCompact_univ_iff, ← hsurj]
  exact hK.image QuotientGroup.continuous_mk

omit [IsTopologicalGroup G] in
private theorem annihilator_discrete (μ : G →ₜ* Multiplicative ℝ) (hproper : IsProperMap μ)
    (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ)) :
    DiscreteTopology (MonogenicAnnihilator γ) := by
  obtain ⟨K, hK, hrep⟩ := modulated_compact_representatives μ γ hγ hproper
  apply discreteTopology_of_isOpen_singleton_one
  let V : Set Circle := {z | 0 < (z : ℂ).re}
  have hV : IsOpen V := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  let T : (MonogenicAnnihilator γ) → C(G, Circle) := fun χ => χ.val.toContinuousMap
  have ht : Continuous T :=
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous.comp continuous_subtype_val
  have hopen : IsOpen {χ : MonogenicAnnihilator γ | MapsTo χ.val K V} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo hK hV).preimage ht
  have he : {χ : MonogenicAnnihilator γ | MapsTo χ.val K V} = {1} := by
    ext χ
    constructor
    · intro h
      have hχ : χ.val γ = 1 := χ.property
      have hall (g : G) : 0 < ((χ.val g : Circle) : ℂ).re := by
        obtain ⟨n, hn⟩ := hrep g
        have ha : χ.val (g / γ ^ n) = χ.val g := by rw [map_div, map_zpow, hχ, one_zpow, div_one]
        have hb : χ.val (g / γ ^ n) ∈ V := h hn
        rw [ha] at hb
        exact hb
      have hr : χ.val.toMonoidHom.range = ⊥ := circle_subgroup_trivial_in_right_halfPlane _
        (by rintro _ ⟨g, rfl⟩; exact hall g)
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      apply ContinuousMonoidHom.ext
      intro g
      change χ.val g = 1
      have hh : χ.val g ∈ χ.val.toMonoidHom.range := ⟨g, rfl⟩
      rwa [hr] at hh
    · rintro rfl
      exact fun _ _ => by change 0 < (1 : ℂ).re; simp
  exact he ▸ hopen

def modulusCharacter (μ : G →ₜ* Multiplicative ℝ) (t : ℝ) : CircleCharacter G where
  toFun g := Circle.exp (t * Multiplicative.toAdd (μ g))
  map_one' := by
    change Circle.exp (t * Multiplicative.toAdd (μ 1)) = 1
    rw [map_one]
    change Circle.exp (t * 0) = 1
    rw [mul_zero, Circle.exp_zero]
  map_mul' a b := by
    rw [map_mul μ a b]
    change Circle.exp (t * (Multiplicative.toAdd (μ a) + Multiplicative.toAdd (μ b))) = _
    rw [mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp ((continuous_toAdd.comp μ.continuous_toFun).const_mul _)

/-- The closed interval of frequencies in the norm-twist component of a character.
The modulation is given in logarithmic coordinates. -/
def modulatedFrequencyBand (μ : G →ₜ* Multiplicative ℝ) (χ : CircleCharacter G)
    (α β : ℝ) : Set (CircleCharacter G) :=
  (fun t => χ * modulusCharacter μ t) '' Icc α β

omit [IsTopologicalGroup G] in
/-- The bounded norm-twist band is compact in the compact-open topology. -/
theorem isCompact_modulatedFrequencyBand (μ : G →ₜ* Multiplicative ℝ)
    (χ : CircleCharacter G) (α β : ℝ) :
    IsCompact (modulatedFrequencyBand μ χ α β) := by
  apply isCompact_Icc.image
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × G =>
    χ p.2 * Circle.exp (p.1 * Multiplicative.toAdd (μ p.2)))
  exact (χ.continuous.comp continuous_snd).mul
    (Circle.exp.continuous.comp
      (continuous_fst.mul (continuous_toAdd.comp (μ.continuous.comp continuous_snd))))

omit [IsTopologicalGroup G] in
/-- §9.3.2.3. The circle-valued frequency band is the imaginary interval
of the complex norm-twist chart. Adapted from original commit cddecc5. -/
theorem mem_modulatedFrequencyBand_iff_cpow (μ : G →ₜ* Multiplicative ℝ)
    (χ ψ : CircleCharacter G) (α β : ℝ) :
    ψ ∈ modulatedFrequencyBand μ χ α β ↔
      ∃ t ∈ Icc α β, ∀ g,
        (ψ g : ℂ) = (χ g : ℂ) *
          (Real.exp (Multiplicative.toAdd (μ g)) : ℂ) ^ ((t : ℂ) * I) := by
  have hpower (t : ℝ) (g : G) :
      (Real.exp (Multiplicative.toAdd (μ g)) : ℂ) ^ ((t : ℂ) * I) =
        (modulusCharacter μ t g : ℂ) := by
    have hpos := Real.exp_pos (Multiplicative.toAdd (μ g))
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, Real.log_exp]
    change _ = ((Circle.exp (t * Multiplicative.toAdd (μ g)) : Circle) : ℂ)
    rw [Circle.coe_exp]
    push_cast
    congr 1
    ring
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, fun g => by rw [hpower]; exact Circle.coe_mul _ _⟩
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, ContinuousMonoidHom.ext fun g => ?_⟩
    apply Subtype.ext
    change ((χ g * modulusCharacter μ t g : Circle) : ℂ) = _
    rw [Circle.coe_mul, h g, hpower]

private def preferredModulatedPhase (ℓ : ℝ) (hℓ : 0 < ℓ) (z : Circle) : ℝ :=
  toIcoMod (div_pos Real.two_pi_pos hℓ) 0 (Complex.arg z / ℓ)

private theorem preferredModulatedPhase_spec {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Circle) :
    preferredModulatedPhase ℓ hℓ z ∈ Ico 0 (2 * Real.pi / ℓ) ∧
      Circle.exp (preferredModulatedPhase ℓ hℓ z * ℓ) = z := by
  have hm := toIcoMod_mem_Ico' (div_pos Real.two_pi_pos hℓ) (Complex.arg z / ℓ)
  refine ⟨hm, ?_⟩
  apply Eq.trans _ (Circle.exp_arg z)
  rw [Circle.exp_eq_exp]
  let n := toIcoDiv (div_pos Real.two_pi_pos hℓ) 0 (Complex.arg z / ℓ)
  refine ⟨-n, ?_⟩
  dsimp only [preferredModulatedPhase]
  rw [← self_sub_toIcoDiv_mul]
  change (Complex.arg z / ℓ - (n : ℝ) * (2 * Real.pi / ℓ)) * ℓ =
    Complex.arg z + ((-n : ℤ) : ℝ) * (2 * Real.pi)
  rw [Int.cast_neg, sub_mul, div_mul_cancel₀ _ hℓ.ne', mul_assoc, div_mul_cancel₀ _ hℓ.ne']
  ring

private theorem phaseTranslate_lattice {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Circle) (c : ℝ) :
    z * Circle.exp (c * ℓ) = 1 ↔
      ∃ m : ℤ, c = (m : ℝ) * (2 * Real.pi / ℓ) - preferredModulatedPhase ℓ hℓ z := by
  let θ := preferredModulatedPhase ℓ hℓ z
  nth_rewrite 1 [← (preferredModulatedPhase_spec hℓ z).2]
  rw [← Circle.exp_add, Circle.exp_eq_one]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply (eq_sub_iff_add_eq.mpr ?_)
    apply (mul_right_cancel₀ hℓ.ne')
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hℓ.ne', add_comm]
    exact hm
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    change θ * ℓ + c * ℓ = _
    rw [hm, sub_mul, mul_assoc, div_mul_cancel₀ _ hℓ.ne']
    ring

private theorem preferredModulatedPhase_unique {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Circle) {c : ℝ}
    (hc : c ∈ Ico 0 (2 * Real.pi / ℓ)) (he : Circle.exp (c * ℓ) = z) :
    c = preferredModulatedPhase ℓ hℓ z := by
  let θ := preferredModulatedPhase ℓ hℓ z
  have hθ : θ ∈ Ico 0 (2 * Real.pi / ℓ) := (preferredModulatedPhase_spec hℓ z).1
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp (he.trans (preferredModulatedPhase_spec hℓ z).2.symm)
  have hπ := Real.two_pi_pos
  have hLo := mul_lt_mul_of_pos_right hc.2 hℓ
  have hHi := mul_lt_mul_of_pos_right hθ.2 hℓ
  rw [div_mul_cancel₀ _ hℓ.ne'] at hLo hHi
  have h₀ : 0 ≤ c * ℓ := mul_nonneg hc.1 hℓ.le
  have h₁ : 0 ≤ θ * ℓ := mul_nonneg hθ.1 hℓ.le
  have hlt : (k : ℝ) < 1 := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_right h hπ.le
    linarith
  have hgt : -1 < (k : ℝ) := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_right h hπ.le
    linarith
  have hlt' : k < 1 := by exact_mod_cast hlt
  have hgt' : -1 < k := by exact_mod_cast hgt
  have hzero : k = 0 := by omega
  rw [hzero, Int.cast_zero, zero_mul, add_zero] at hk
  exact mul_right_cancel₀ hℓ.ne' hk

/-- A circle value has a unique frequency in the normalized half-open period. -/
theorem existsUnique_circle_log_period {L : ℝ} (hL : 0 < L) (a : Circle) :
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = a :=
  ⟨preferredModulatedPhase L hL a, preferredModulatedPhase_spec hL a,
    fun _ ht => preferredModulatedPhase_unique hL a ht.1 ht.2⟩

def modulatedKernelInclusion (μ : G →ₜ* Multiplicative ℝ) : μ.toMonoidHom.ker →ₜ* G :=
  ⟨μ.toMonoidHom.ker.subtype, continuous_subtype_val⟩

/-- The projection onto the modulus kernel determined by a section. -/
def modulatedKernelProjection (μ : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t) :
    G →ₜ* μ.toMonoidHom.ker := by
  have hker (g : G) : g / τ (μ g) ∈ μ.toMonoidHom.ker := by
    change μ (g / τ (μ g)) = 1
    rw [map_div μ, hτ, div_self']
  let p : G → μ.toMonoidHom.ker := fun g => ⟨g / τ (μ g), hker g⟩
  refine { toFun := p
           map_one' := ?_
           map_mul' := ?_
           continuous_toFun := ?_ }
  · apply Subtype.ext
    change (1 : G) / τ (μ 1) = 1
    rw [map_one μ, map_one τ, div_one]
  · intro g h
    apply Subtype.ext
    change (g * h) / τ (μ (g * h)) = (g / τ (μ g)) * (h / τ (μ h))
    rw [map_mul μ, map_mul τ, mul_div_mul_comm]
  · exact (continuous_id.div' (τ.continuous_toFun.comp μ.continuous_toFun)).subtype_mk hker

/-- A continuous section of the modulus extends each kernel character. -/
def extendModulatedCharacter (μ : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (ω : CircleCharacter μ.toMonoidHom.ker) : CircleCharacter G :=
  ω.comp (modulatedKernelProjection μ τ hτ)

/-- Extension along the norm-one retraction is continuous in the
compact-open topology on characters. -/
theorem continuous_extendModulatedCharacter (μ : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t) :
    Continuous (extendModulatedCharacter μ τ hτ) :=
  (PontryaginDual.map (modulatedKernelProjection μ τ hτ)).continuous

theorem extendModulatedCharacter_restrict (μ : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (ω : CircleCharacter μ.toMonoidHom.ker) :
    (extendModulatedCharacter μ τ hτ ω).comp (modulatedKernelInclusion μ) = ω := by
  apply ContinuousMonoidHom.ext
  intro g
  change ω (modulatedKernelProjection μ τ hτ g) = ω g
  congr 1
  apply Subtype.ext
  have hg : μ g = 1 := g.property
  change (g : G) / τ (μ g) = g
  rw [hg, map_one, div_one]

theorem modulatedCharacter_eq_mul_modulus
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (χ ψ : CircleCharacter G)
    (h : ψ.comp (modulatedKernelInclusion μ) = χ.comp (modulatedKernelInclusion μ)) :
    ∃ c : ℝ, ψ = χ * modulusCharacter μ c := by
  let ν := ψ / χ
  let c := Multiplicative.toAdd (characterSlope τ ν)
  refine ⟨c, ?_⟩
  apply ContinuousMonoidHom.ext
  intro g
  let k := modulatedKernelProjection μ τ hτ g
  have hk : (k : G) = g / τ (μ g) := rfl
  have he : τ (μ g) * (k : G) = g := by rw [hk, mul_comm, div_mul_cancel]
  have hv : ν (k : G) = 1 := by
    change ψ (k : G) / χ (k : G) = 1
    have h' : ψ (k : G) = χ (k : G) :=
      DFunLike.congr_fun h k
    rw [h', div_self']
  have hc : ν (τ (μ g)) = Circle.exp (c * Multiplicative.toAdd (μ g)) :=
    characterSlope_eq_exp τ ν (Multiplicative.toAdd (μ g))
  have hs : ν g = Circle.exp (c * Multiplicative.toAdd (μ g)) := by
    calc
      ν g = ν (τ (μ g) * (k : G)) := congrArg ν he.symm
      _ = _ := by rw [map_mul, hv, mul_one]; exact hc
  change ψ g = χ g * Circle.exp (c * Multiplicative.toAdd (μ g))
  exact div_eq_iff_eq_mul'.mp hs

omit [IsTopologicalGroup G] in
private theorem modulatedModulusCharacter_parameter_injective
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t) :
    Injective (modulusCharacter μ) := by
  intro c d h
  have hc (t : ℝ) :
      modulusCharacter μ c (τ (Multiplicative.ofAdd t)) = Circle.exp (c * t) := by
    change Circle.exp (c * Multiplicative.toAdd (μ (τ (Multiplicative.ofAdd t)))) = _
    rw [hτ]
    rfl
  have hd (t : ℝ) :
      modulusCharacter μ c (τ (Multiplicative.ofAdd t)) = Circle.exp (d * t) := by
    rw [h]
    change Circle.exp (d * Multiplicative.toAdd (μ (τ (Multiplicative.ofAdd t)))) = _
    rw [hτ]
    rfl
  exact (characterSlope_unique τ _ c hc).symm.trans (characterSlope_unique τ _ d hd)

open scoped ContDiff in
/-- A smooth cutoff along each frequency component, supported in the
closed outer band and equal to one on the smaller band of Corollary 9.3.2.3. -/
theorem exists_modulatedFrequencyBand_cutoff
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    [CompactSpace μ.toMonoidHom.ker] (χ : CircleCharacter G) {α β ε : ℝ}
    (hε : 0 < ε) (hwidth : α + ε < β - ε) :
    ∃ F : C(CircleCharacter G, ℂ),
      tsupport F ⊆ modulatedFrequencyBand μ χ α β ∧
      HasCompactSupport F ∧
      Set.EqOn F 1 (modulatedFrequencyBand μ χ (α + ε) (β - ε)) ∧
      ∀ ψ : CircleCharacter G, ContDiff ℝ ∞ (fun t : ℝ => F (ψ * modulusCharacter μ t)) := by
  let center := (α + β) / 2
  let radius := (β - α) / 2
  let b : ContDiffBump center := ⟨radius - ε, radius, by dsimp [radius]; linarith, by linarith⟩
  let K := μ.toMonoidHom.ker
  let Iₖ := modulatedKernelInclusion μ
  let W : Set (CircleCharacter G) := {ψ | ψ.comp Iₖ = χ.comp Iₖ}
  let p (ψ : CircleCharacter G) := Multiplicative.toAdd (characterSlope τ (ψ / χ))
  have hp : Continuous p := (continuous_toAdd.comp (characterSlope_continuous τ)).comp
    (continuous_id.div' continuous_const)
  have hW : IsClopen W := by
    haveI : DiscreteTopology (CircleCharacter K) :=
      inferInstanceAs (DiscreteTopology (PontryaginDual K))
    exact (isClopen_discrete ({χ.comp Iₖ} : Set (CircleCharacter K))).preimage
      (ContinuousMonoidHom.continuous_comp_left Iₖ)
  let f (ψ : CircleCharacter G) := (b (p ψ) : ℂ)
  let F : C(CircleCharacter G, ℂ) :=
    ⟨W.indicator f, hW.continuous_indicator
      (Complex.continuous_ofReal.comp ((b.contDiff (n := ⊤)).continuous.comp hp))⟩
  have hpmod (t : ℝ) : Multiplicative.toAdd (characterSlope τ (modulusCharacter μ t)) = t := by
    apply characterSlope_unique
    intro x
    change Circle.exp (t * Multiplicative.toAdd (μ (τ (Multiplicative.ofAdd x)))) = _
    rw [hτ]
    rfl
  have hpmul (ψ : CircleCharacter G) (t : ℝ) : p (ψ * modulusCharacter μ t) = p ψ + t := by
    dsimp only [p]
    rw [mul_div_right_comm, map_mul]
    change _ + Multiplicative.toAdd (characterSlope τ (modulusCharacter μ t)) = _ + t
    rw [hpmod]
  have hrem (ψ : CircleCharacter G) (t : ℝ) :
      (ψ * modulusCharacter μ t) ∈ W ↔ ψ ∈ W := by
    have h : (ψ * modulusCharacter μ t).comp Iₖ = ψ.comp Iₖ := by
      apply ContinuousMonoidHom.ext
      intro x
      change ψ x * Circle.exp (t * Multiplicative.toAdd (μ x)) = ψ x
      rw [show μ x = 1 from x.property]
      simp
    change ((ψ * modulusCharacter μ t).comp Iₖ = χ.comp Iₖ) ↔
      (ψ.comp Iₖ = χ.comp Iₖ)
    rw [h]
  have hpχ : p χ = 0 := by simp [p]
  have hsupport : Function.support F ⊆ modulatedFrequencyBand μ χ α β := by
    intro ψ hψ
    have hfne : W.indicator f ψ ≠ 0 := hψ
    have hmem : ψ ∈ W := by
      by_contra h
      exact hfne (indicator_of_notMem h f)
    obtain ⟨t, rfl⟩ := modulatedCharacter_eq_mul_modulus μ τ hτ χ ψ hmem
    rw [indicator_of_mem hmem] at hfne
    have hbt : b t ≠ 0 := by
      simpa [f, hpmul, hpχ] using hfne
    have hbball : t ∈ Metric.ball center radius := by
      have hbmem : t ∈ Function.support b := hbt
      rwa [b.support_eq] at hbmem
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hbball
    exact ⟨t, ⟨by dsimp [center, radius] at hbball; linarith,
      by dsimp [center, radius] at hbball; linarith⟩, rfl⟩
  have hcompact := isCompact_modulatedFrequencyBand μ χ α β
  have hts : tsupport F ⊆ modulatedFrequencyBand μ χ α β :=
    closure_minimal hsupport hcompact.isClosed
  refine ⟨F, hts, hcompact.of_isClosed_subset isClosed_closure hts, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hmem := (hrem χ t).2 (show χ ∈ W from rfl)
    change W.indicator f (χ * modulusCharacter μ t) = 1
    rw [indicator_of_mem hmem]
    change (b (p (χ * modulusCharacter μ t)) : ℂ) = 1
    rw [hpmul, hpχ, zero_add]
    have hbball : t ∈ Metric.closedBall center (radius - ε) := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      dsimp [center, radius]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact_mod_cast b.one_of_mem_closedBall hbball
  · intro ψ
    change ContDiff ℝ ∞ (fun t : ℝ => W.indicator f (ψ * modulusCharacter μ t))
    by_cases h : ψ ∈ W
    · have hfun : (fun t : ℝ => W.indicator f (ψ * modulusCharacter μ t)) =
          fun t : ℝ => (b (p ψ + t) : ℂ) := by
        funext t
        rw [indicator_of_mem ((hrem ψ t).2 h)]
        simp only [f, hpmul]
      rw [hfun]
      exact Complex.ofRealCLM.contDiff.comp
        (b.contDiff.comp (contDiff_const.add contDiff_id))
    · have hfun : (fun t : ℝ => W.indicator f (ψ * modulusCharacter μ t)) =
          fun _ : ℝ => (0 : ℂ) := by
        funext t
        exact indicator_of_notMem (fun ht => h ((hrem ψ t).1 ht)) f
      rw [hfun]
      exact contDiff_const

/-- Corrected Lemma 4.4.2.5. The preferred phase is subtracted when twisting
a representative to a character trivial on the monogenic group. -/
theorem modulated_annihilator_parameterization
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (hproper : IsProperMap μ) (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ))
    (lift : CircleCharacter μ.toMonoidHom.ker → CircleCharacter G)
    (hlift : ∀ ω, (lift ω).comp (modulatedKernelInclusion μ) = ω) :
    let ℓ := Multiplicative.toAdd (μ γ)
    let θ := fun ω => preferredModulatedPhase ℓ hγ (lift ω γ)
    let param := fun (p : CircleCharacter μ.toMonoidHom.ker × ℤ) =>
      lift p.1 * modulusCharacter μ ((p.2 : ℝ) * (2 * Real.pi / ℓ) - θ p.1)
    (∀ ω, ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / ℓ) ∧ Circle.exp (t * ℓ) = lift ω γ) ∧
    Injective param ∧ range param = (MonogenicAnnihilator γ : Set (CircleCharacter G)) ∧
    DiscreteTopology (MonogenicAnnihilator γ) := by
  dsimp only
  let ℓ := Multiplicative.toAdd (μ γ)
  let θ := fun ω => preferredModulatedPhase ℓ hγ (lift ω γ)
  let param := fun (p : CircleCharacter μ.toMonoidHom.ker × ℤ) =>
    lift p.1 * modulusCharacter μ ((p.2 : ℝ) * (2 * Real.pi / ℓ) - θ p.1)
  have hparam (p : CircleCharacter μ.toMonoidHom.ker × ℤ) :
      (param p).comp (modulatedKernelInclusion μ) = p.1 := by
    apply ContinuousMonoidHom.ext
    intro g
    have hω : lift p.1 (g : G) = p.1 g := DFunLike.congr_fun (hlift _) g
    have hg : μ g = 1 := g.property
    change lift p.1 (g : G) * Circle.exp (((p.2 : ℝ) * (2 * Real.pi / ℓ) - θ p.1) *
      Multiplicative.toAdd (μ g)) = p.1 g
    rw [hω, hg]
    simp
  refine ⟨fun ω => ⟨θ ω, preferredModulatedPhase_spec hγ _, fun t ht =>
      preferredModulatedPhase_unique hγ _ ht.1 ht.2⟩, ?_, ?_, annihilator_discrete μ hproper γ hγ⟩
  · rintro ⟨ω, m⟩ ⟨ψ, n⟩ h
    have hRestr := congrArg (fun χ : CircleCharacter G => χ.comp (modulatedKernelInclusion μ)) h
    have he : ω = ψ := (hparam (ω,m)).symm.trans (hRestr.trans (hparam (ψ,n)))
    subst ψ
    have hM := mul_left_cancel h
    have hmn := modulatedModulusCharacter_parameter_injective μ τ hτ hM
    have hreal : (m : ℝ) = (n : ℝ) := mul_right_cancel₀
      (div_pos Real.two_pi_pos hγ).ne' (by linarith)
    exact Prod.ext rfl (by exact_mod_cast hreal)
  · ext χ
    constructor
    · rintro ⟨⟨ω, m⟩, rfl⟩
      change lift ω γ * Circle.exp (((m : ℝ) * (2 * Real.pi / ℓ) - θ ω) * ℓ) = 1
      exact (phaseTranslate_lattice hγ _ _).mpr ⟨m, rfl⟩
    · intro hχ
      let ω := χ.comp (modulatedKernelInclusion μ)
      obtain ⟨c, hc⟩ := modulatedCharacter_eq_mul_modulus μ τ hτ (lift ω) χ (hlift ω).symm
      have hγ' : χ γ = 1 := hχ
      rw [hc] at hγ'
      change lift ω γ * Circle.exp (c * ℓ) = 1 at hγ'
      obtain ⟨m, hm⟩ := (phaseTranslate_lattice hγ _ _).mp hγ'
      refine ⟨(ω, m), ?_⟩
      change lift ω * modulusCharacter μ ((m : ℝ) * (2 * Real.pi / ℓ) - θ ω) = χ
      rw [← hm, ← hc]

/-- The corrected cyclic character descends to the actual quotient by the generator. -/
def modulatedCyclicCharacter
    (μ : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ))
    (χ : CircleCharacter G) (n : ℤ) : CircleCharacter (G ⧸ Subgroup.zpowers γ) := by
  let L := Multiplicative.toAdd (μ γ)
  let θ := preferredModulatedPhase L hγ (χ γ)
  let ψ := χ * modulusCharacter μ ((n : ℝ) * (2 * Real.pi / L) - θ)
  have hψ : ψ ∈ MonogenicAnnihilator γ := by
    change χ γ * Circle.exp (((n : ℝ) * (2 * Real.pi / L) - θ) * L) = 1
    exact (phaseTranslate_lattice hγ _ _).mpr ⟨n, rfl⟩
  let descended := QuotientGroup.lift (Subgroup.zpowers γ) ψ.toMonoidHom (by
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (mem_monogenicAnnihilator_iff ψ γ).mp hψ m)
  exact ⟨descended, QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp ψ.continuous⟩

/-- The pullback of the cyclic fibre has an affine frequency parameter. -/
theorem modulatedCyclicCharacter_affine
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    (χ : CircleCharacter G) :
    ∃ a : ℝ, ∀ (n : ℤ) (g : G),
      modulatedCyclicCharacter m γ hγ χ n (QuotientGroup.mk g) =
        (χ * modulusCharacter m (a + (2 * Real.pi / (m γ).toAdd) * (n : ℝ))) g := by
  let θ := preferredModulatedPhase (m γ).toAdd hγ (χ γ)
  let d := 2 * Real.pi / (m γ).toAdd
  refine ⟨-θ, fun n g ↦ ?_⟩
  change χ g * Circle.exp (((n : ℝ) * d - θ) * (m g).toAdd) =
    χ g * Circle.exp ((-θ + d * (n : ℝ)) * (m g).toAdd)
  congr 2
  ring

/-- Successive cyclic quotient characters differ by the integral powers of
a single character. The compact character lift is fixed along this line. -/
theorem modulatedCyclicCharacter_line
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    (χ : CircleCharacter G) (n : ℤ) :
    modulatedCyclicCharacter m γ hγ χ n =
      modulatedCyclicCharacter m γ hγ χ 0 *
        ((modulatedCyclicCharacter m γ hγ χ 0)⁻¹ * modulatedCyclicCharacter m γ hγ χ 1) ^ n := by
  apply ContinuousMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  let L := Multiplicative.toAdd (m γ)
  let θ := preferredModulatedPhase L hγ (χ γ)
  let y := Multiplicative.toAdd (m x)
  let A := χ x * Circle.exp (-θ * y)
  let B := Circle.exp ((2 * Real.pi / L) * y)
  have he (k : ℤ) :
      modulatedCyclicCharacter m γ hγ χ k (QuotientGroup.mk x) = A * B ^ k := by
    change χ x * Circle.exp (((k : ℝ) * (2 * Real.pi / L) - θ) * y) = _
    have h : ((k : ℝ) * (2 * Real.pi / L) - θ) * y =
        -θ * y + k • ((2 * Real.pi / L) * y) := by
      rw [zsmul_eq_mul]
      ring
    rw [h, Circle.exp_add, Circle.exp_zsmul, mul_assoc]
  let e : CircleCharacter (G ⧸ Subgroup.zpowers γ) →* Circle :=
    { toFun := fun c ↦ c (QuotientGroup.mk x)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  change e (modulatedCyclicCharacter m γ hγ χ n) = e (_ * _ ^ n)
  rw [map_mul e, map_zpow e, map_mul e, map_inv e]
  change modulatedCyclicCharacter m γ hγ χ n (QuotientGroup.mk x) =
    modulatedCyclicCharacter m γ hγ χ 0 (QuotientGroup.mk x) *
      ((modulatedCyclicCharacter m γ hγ χ 0 (QuotientGroup.mk x))⁻¹ *
        modulatedCyclicCharacter m γ hγ χ 1 (QuotientGroup.mk x)) ^ n
  simp only [he, zpow_zero, zpow_one, mul_one, inv_mul_cancel_left]

/-- The chosen lifts and the integer frequencies enumerate every quotient
character exactly once. -/
theorem modulatedCyclicCharacter_bijective
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : Function.RightInverse τ m)
    (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    (lift : CircleCharacter m.toMonoidHom.ker → CircleCharacter G)
    (hlift : ∀ ω, (lift ω).comp (modulatedKernelInclusion m) = ω) :
    Function.Bijective (fun j : CircleCharacter m.toMonoidHom.ker × ℤ ↦
      modulatedCyclicCharacter m γ hγ (lift j.1) j.2) := by
  let Q := G ⧸ Subgroup.zpowers γ
  let q : G →ₜ* Q := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let p (j : CircleCharacter m.toMonoidHom.ker × ℤ) :=
    modulatedCyclicCharacter m γ hγ (lift j.1) j.2
  let a (j : CircleCharacter m.toMonoidHom.ker × ℤ) :=
    lift j.1 * modulusCharacter m ((j.2 : ℝ) * (2 * Real.pi / Multiplicative.toAdd (m γ)) -
      preferredModulatedPhase (Multiplicative.toAdd (m γ)) hγ (lift j.1 γ))
  have hparam : Function.Injective a ∧ Set.range a = (MonogenicAnnihilator γ : Set _) :=
    let h := modulated_annihilator_parameterization m τ hτ hm γ hγ lift hlift
    ⟨h.2.1, h.2.2.1⟩
  have hp (j) : (p j).comp q = a j := by
    apply ContinuousMonoidHom.ext
    intro x
    rfl
  refine ⟨fun i j hij ↦ hparam.1 ((hp i).symm.trans
    ((congrArg (fun ψ : CircleCharacter Q ↦ ψ.comp q) hij).trans (hp j))), ?_⟩
  intro ψ
  have hψ : ψ.comp q ∈ (MonogenicAnnihilator γ : Set _) := by
    have hg : q γ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers γ)
    change ψ (q γ) = 1
    rw [hg, map_one]
  obtain ⟨j, hj⟩ := hparam.2.symm.subset hψ
  refine ⟨j, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact DFunLike.congr_fun ((hp j).trans hj) y

omit [IsTopologicalGroup G] in
/-- The manuscript's compact characters and integer frequencies admit an enumeration. -/
theorem modulatedCyclicIndex_enumerable [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) :
    Nonempty (ℕ ≃ CircleCharacter m.toMonoidHom.ker × ℤ) := by
  let K := m.toMonoidHom.ker
  have hK : IsCompact (K : Set G) :=
    hm.isCompact_preimage (K := {1}) isCompact_singleton
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : LocallyCompactSpace K := hK.isClosed.locallyCompactSpace
  letI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  letI : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  letI : SecondCountableTopology (PontryaginDual K) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  letI : Countable (PontryaginDual K) := countable_of_Lindelof_of_discrete
  change Nonempty (ℕ ≃ PontryaginDual K × ℤ)
  exact nonempty_equiv_of_countable

/-- Equation (4.4.2.5) in logarithmic coordinates for the corrected character.
The conjugate character gives the exponential used for the basis. Adapted from
original commit 233c0de. -/
theorem modulatedCyclicExponential_split
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ)) (χ : CircleCharacter G)
    (b : ℝ) (hb : ∀ t : ℝ, χ (τ (Multiplicative.ofAdd t)) = Circle.exp (b * t))
    (n : ℤ) (t : ℝ) (k : μ.toMonoidHom.ker) :
    let L := Multiplicative.toAdd (μ γ)
    let θ := preferredModulatedPhase L hγ (χ γ)
    star (modulatedCyclicCharacter μ γ hγ χ n
      (QuotientGroup.mk (τ (Multiplicative.ofAdd t) * k.val)) : ℂ) =
      star (χ k.val : ℂ) * (Circle.exp ((θ - (n : ℝ) * (2 * Real.pi / L) - b) * t) : ℂ) := by
  dsimp only
  let L := Multiplicative.toAdd (μ γ)
  let θ := preferredModulatedPhase L hγ (χ γ)
  have hlog : Multiplicative.toAdd (μ (τ (Multiplicative.ofAdd t) * k.val)) = t := by
    rw [map_mul, hτ, show μ k.val = 1 from k.property, mul_one]
    rfl
  change star ((χ (τ (Multiplicative.ofAdd t) * k.val) *
    Circle.exp (((n : ℝ) * (2 * Real.pi / L) - θ) *
      Multiplicative.toAdd (μ (τ (Multiplicative.ofAdd t) * k.val))) : Circle) : ℂ) = _
  rw [hlog, map_mul, hb]
  have he : (Circle.exp (b * t) * χ k.val *
      Circle.exp (((n : ℝ) * (2 * Real.pi / L) - θ) * t))⁻¹ =
      (χ k.val)⁻¹ * Circle.exp ((θ - (n : ℝ) * (2 * Real.pi / L) - b) * t) := by
    simp only [mul_inv, ← Circle.exp_neg]
    calc
      Circle.exp (-(b * t)) * (χ k.val)⁻¹ *
          Circle.exp (-(((n : ℝ) * (2 * Real.pi / L) - θ) * t)) =
        (χ k.val)⁻¹ * (Circle.exp (-(b * t)) *
          Circle.exp (-(((n : ℝ) * (2 * Real.pi / L) - θ) * t))) := by ac_rfl
      _ = _ := by rw [← Circle.exp_add]; congr 2; ring
  simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.star_def] using
    congrArg (fun z : Circle => (z : ℂ)) he

/-- Characters in the union of the cyclic annihilator fibres, with a fixed
restriction to the kernel of the modulus, as in (4.6.1.12). -/
def modulatedPeriodicSpectrum {ι : Type*} (μ : G →ₜ* Multiplicative ℝ)
    (ω : CircleCharacter μ.toMonoidHom.ker) (γ : ι → G) : Set (CircleCharacter G) :=
  ⋃ i, {χ | χ ∈ MonogenicAnnihilator (γ i) ∧ χ.comp (modulatedKernelInclusion μ) = ω}

/-- Multiplicity counts the indices of the fibres containing a character.
Adapted from `Ch04_PeriodicSchauderBases/Sec6.lean` at 770033a under Apache-2.0. -/
def modulatedPeriodicMultiplicity {ι : Type*} [Fintype ι] (μ : G →ₜ* Multiplicative ℝ)
    (ω : CircleCharacter μ.toMonoidHom.ker) (γ : ι → G) (χ : CircleCharacter G) : ℕ := by
  classical
  exact (Finset.univ.filter fun i =>
    χ ∈ MonogenicAnnihilator (γ i) ∧ χ.comp (modulatedKernelInclusion μ) = ω).card

omit [IsTopologicalGroup G] in
/-- Equations (4.6.1.12)–(4.6.1.13). A character is in the spectrum
exactly when its multiplicity is positive. -/
theorem mem_modulatedPeriodicSpectrum_iff {ι : Type*} [Fintype ι]
    (μ : G →ₜ* Multiplicative ℝ) (ω : CircleCharacter μ.toMonoidHom.ker)
    (γ : ι → G) (χ : CircleCharacter G) :
    χ ∈ modulatedPeriodicSpectrum μ ω γ ↔ 0 < modulatedPeriodicMultiplicity μ ω γ χ := by
  classical
  simp only [modulatedPeriodicSpectrum, modulatedPeriodicMultiplicity, mem_iUnion,
    mem_ofPred_eq, Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and]

omit [IsTopologicalGroup G] in
/-- Repeating a generator counts every copy for characters in its fibre. -/
theorem modulatedPeriodicMultiplicity_repeat {ι : Type*} [Fintype ι]
    (μ : G →ₜ* Multiplicative ℝ) (ω : CircleCharacter μ.toMonoidHom.ker)
    (γ : G) (χ : CircleCharacter G)
    (hχ : χ ∈ MonogenicAnnihilator γ) (hω : χ.comp (modulatedKernelInclusion μ) = ω) :
    modulatedPeriodicMultiplicity μ ω (fun _ : ι => γ) χ = Fintype.card ι := by
  classical
  unfold modulatedPeriodicMultiplicity
  rw [Finset.filter_eq_self.mpr (fun _ _ => And.intro hχ hω), Finset.card_univ]

omit [IsTopologicalGroup G] in
/-- The finite periodic spectrum in (4.6.1.12) is discrete under the
proper-modulus hypothesis and positive logarithmic periods. -/
theorem modulatedPeriodicSpectrum_isDiscrete {ι : Type*} [Finite ι]
    (μ : G →ₜ* Multiplicative ℝ) (ω : CircleCharacter μ.toMonoidHom.ker)
    (γ : ι → G) (hproper : IsProperMap μ)
    (hγ : ∀ i, 0 < Multiplicative.toAdd (μ (γ i))) :
    IsDiscrete (modulatedPeriodicSpectrum μ ω γ) := by
  apply IsDiscrete.iUnion
  · intro i
    exact (show IsDiscrete (MonogenicAnnihilator (γ i) : Set (CircleCharacter G))
      from isDiscrete_iff_discreteTopology.mpr (annihilator_discrete μ hproper (γ i) (hγ i))).mono (fun _ h => h.1)
  · intro i
    have heval (g : G) : Continuous (fun χ : CircleCharacter G => χ g) := by
      have h : Continuous (fun f : C(G, Circle) => f g) := continuous_eval_const g
      exact h.comp (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
    have he : {χ : CircleCharacter G |
        χ ∈ MonogenicAnnihilator (γ i) ∧ χ.comp (modulatedKernelInclusion μ) = ω} =
        {χ | χ (γ i) = 1} ∩ ⋂ u : μ.toMonoidHom.ker, {χ | χ u.val = ω u} := by
      ext χ
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
      exact and_congr Iff.rfl ⟨fun h u => DFunLike.congr_fun h u, fun h => ContinuousMonoidHom.ext (fun u => h u)⟩
    rw [he]
    exact (isClosed_eq (heval (γ i)) continuous_const).inter
      (isClosed_iInter fun u => isClosed_eq (heval u.val) continuous_const)

/-- A moment index consists of a character and a logarithmic degree below its multiplicity. -/
def ModulatedPeriodicMomentIndex {ι : Type*} [Fintype ι] (μ : G →ₜ* Multiplicative ℝ)
    (ω : CircleCharacter μ.toMonoidHom.ker) (γ : ι → G) :=
  {p : CircleCharacter G × ℕ // p.2 < modulatedPeriodicMultiplicity μ ω γ p.1}

/-- The integer phases parametrize the actual cyclic annihilator fibre with
fixed norm-one character. The fibre statement of 4.6.1.5 is also proved in
mccorvie/riemann-masullo, commit 1febccb (Apache-2.0). -/
theorem modulatedPeriodicFrequency_bijective
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (ω : CircleCharacter μ.toMonoidHom.ker) (γ : G)
    (hγ : 0 < Multiplicative.toAdd (μ γ)) :
    let χ := extendModulatedCharacter μ τ hτ ω
    let L := Multiplicative.toAdd (μ γ)
    let θ := preferredModulatedPhase L hγ (χ γ)
    let ξ (m : ℤ) := χ * modulusCharacter μ ((m : ℝ) * (2 * Real.pi / L) - θ)
    Injective ξ ∧ range ξ = {ψ | ψ ∈ MonogenicAnnihilator γ ∧
      ψ.comp (modulatedKernelInclusion μ) = ω} := by
  intro χ L θ ξ
  constructor
  · intro m n h
    have hs := modulatedModulusCharacter_parameter_injective μ τ hτ (mul_left_cancel h)
    have hmn : (m : ℝ) = (n : ℝ) := mul_right_cancel₀
      (div_pos Real.two_pi_pos hγ).ne' (by linarith)
    exact_mod_cast hmn
  · ext ψ
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨?_, ?_⟩
      · change χ γ * Circle.exp (((m : ℝ) * (2 * Real.pi / L) - θ) * L) = 1
        exact (phaseTranslate_lattice hγ _ _).mpr ⟨m, rfl⟩
      · apply ContinuousMonoidHom.ext
        intro u
        have hχ := DFunLike.congr_fun (extendModulatedCharacter_restrict μ τ hτ ω) u
        change χ u.val = ω u at hχ
        change χ u.val * Circle.exp (((m : ℝ) * (2 * Real.pi / L) - θ) *
          Multiplicative.toAdd (μ u.val)) = ω u
        rw [show μ u.val = 1 from u.property]
        simpa using hχ
    · rintro ⟨hψ, hω⟩
      obtain ⟨c, hc⟩ := modulatedCharacter_eq_mul_modulus μ τ hτ χ ψ
        (hω.trans (extendModulatedCharacter_restrict μ τ hτ ω).symm)
      have hv : χ γ * Circle.exp (c * L) = 1 := by
        have h : ψ γ = 1 := hψ
        rw [hc] at h
        exact h
      obtain ⟨m, hm⟩ := (phaseTranslate_lattice hγ _ _).mp hv
      exact ⟨m, by rw [hc]; unfold ξ; rw [hm]⟩

/-- The moment index in 4.6.1.5 admits an enumeration for any nonempty finite family.
Adapted from mccorvie/riemann-masullo, commit 79eb594, under Apache-2.0. -/
theorem modulatedPeriodicMomentIndex_enumerable {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, μ (τ t) = t)
    (ω : CircleCharacter μ.toMonoidHom.ker) (γ : ι → G)
    (hγ : ∀ i, 0 < Multiplicative.toAdd (μ (γ i))) :
    Nonempty (ℕ ≃ ModulatedPeriodicMomentIndex μ ω γ) := by
  classical
  let J := ModulatedPeriodicMomentIndex μ ω γ
  let χ := extendModulatedCharacter μ τ hτ ω
  let L (i : ι) := Multiplicative.toAdd (μ (γ i))
  let θ (i : ι) := preferredModulatedPhase (L i) (hγ i) (χ (γ i))
  let ξ (i : ι) (m : ℤ) :=
    χ * modulusCharacter μ ((m : ℝ) * (2 * Real.pi / L i) - θ i)
  have hfibre (i : ι) : Injective (ξ i) ∧
      range (ξ i) = {ψ | ψ ∈ MonogenicAnnihilator (γ i) ∧
        ψ.comp (modulatedKernelInclusion μ) = ω} :=
    modulatedPeriodicFrequency_bijective μ τ hτ ω (γ i) (hγ i)
  have hrepr (j : J) : ∃ i m, ξ i m = j.val.1 := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      ((mem_modulatedPeriodicSpectrum_iff μ ω γ j.val.1).mpr ((Nat.zero_le _).trans_lt j.property))
    have hm : j.val.1 ∈ range (ξ i) := by
      rw [(hfibre i).2]
      exact hi
    obtain ⟨m, hm⟩ := hm
    exact ⟨i, m, hm⟩
  choose i m hrepr using hrepr
  have hcount : Countable J := (show Injective (fun j : J => (i j, m j, j.val.2)) from by
    intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hi, hm, hd⟩ := h
    exact Subtype.ext (Prod.ext ((hrepr a).symm.trans (by rw [hi, hm, hrepr b])) hd)).countable
  let k : ι := Classical.choice ‹Nonempty ι›
  let f (n : ℕ) : J := ⟨(ξ k n, 0), by
    apply (mem_modulatedPeriodicSpectrum_iff μ ω γ _).mp
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [← (hfibre k).2]
    exact ⟨n, rfl⟩⟩
  have hinfinite : Infinite J := Infinite.of_injective f (by
    intro a b h
    exact_mod_cast (hfibre k).1 (congrArg (fun j : J => j.val.1) h))
  exact nonempty_equiv_of_countable

/-- The printed positive phase sends a character of value i at the generator
to one of value -1, so it fails the annihilator equation. -/
theorem printed_positive_phase_twist_fails :
    Circle.exp (Real.pi / 2) * Circle.exp (Real.pi / 2) ≠ 1 := by
  rw [← Circle.exp_add, show Real.pi / 2 + Real.pi / 2 = Real.pi by ring]
  exact Circle.exp_pi_ne_one

end

end Masullo
