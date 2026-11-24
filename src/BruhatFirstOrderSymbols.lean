import BruhatDirectionalDerivatives
import FourierSymbols
import PontryaginDuality

open Function Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Continuous homomorphisms from a multiplicative group to the additive
real line, with the pointwise real vector space structure. -/
def continuousRealHomSubmodule (H : Type*) [Monoid H] [TopologicalSpace H] :
    Submodule ℝ (H → ℝ) where
  carrier := {f | Continuous f ∧ ∀ x y, f (x * y) = f x + f y}
  zero_mem' := ⟨continuous_const, by simp⟩
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun x y ↦ by
    change f (x * y) + g (x * y) = (f x + g x) + (f y + g y)
    simp only [hf.2, hg.2]
    ring⟩
  smul_mem' c _ hf := ⟨continuous_const.mul hf.1, fun x y ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2, mul_add]⟩

/-- The real span of invariant first-order endomorphisms, as in D.1.6.8(1). -/
def bruhatFirstOrderReal : Submodule ℝ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Submodule.span ℝ (range (bruhatFirstOrder (G := G)))

/-- The sum and scaling laws for one-parameter subgroups realize every real
first-order operator by a single direction. -/
theorem bruhatFirstOrderReal_represent (D : bruhatFirstOrderReal (G := G)) :
    ∃ a : Multiplicative ℝ →ₜ* G, D.val = bruhatFirstOrder a := by
  have h : D.val ∈ Submodule.span ℝ (range (bruhatFirstOrder (G := G))) := D.property
  generalize D.val = x at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩
  | zero =>
    exact ⟨(1 : Multiplicative ℝ →ₜ* G).comp (realParameterScale 0), by
      rw [bruhatFirstOrder_scale, zero_smul]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, rfl⟩ := ihx
    obtain ⟨b, rfl⟩ := ihy
    exact ⟨a * b, (bruhatFirstOrder_mul a b).symm⟩
  | smul c x hx ih =>
    obtain ⟨a, rfl⟩ := ih
    exact ⟨a.comp (realParameterScale c), (bruhatFirstOrder_scale c a).symm⟩

private def smoothCharacter (χ : PontryaginDual G) : bruhatSmoothSubmodule (G := G) :=
  ⟨fun x ↦ (χ x : ℂ), pontryaginDual_mem_bruhatSmooth χ⟩

private def bruhatReadFrequency :
    Module.End ℂ (bruhatSmoothSubmodule (G := G)) →ₗ[ℝ] (PontryaginDual G → ℝ) where
  toFun D χ := ((D (smoothCharacter χ)).val 1).im / (2 * Real.pi)
  map_add' D E := by
    funext χ
    change (_ + _ : ℂ).im / (2 * Real.pi) = _
    rw [Complex.add_im, add_div]
    rfl
  map_smul' b D := by
    funext χ
    change (b • (_ : ℂ)).im / (2 * Real.pi) = b * _
    rw [Complex.smul_im, smul_eq_mul, mul_div_assoc]

private theorem bruhatReadFrequency_firstOrder (a : Multiplicative ℝ →ₜ* G) (χ : PontryaginDual G) :
    bruhatReadFrequency (bruhatFirstOrder a) χ =
      (characterSlope a χ).toAdd / (2 * Real.pi) := by
  have h := (directionalDeriv_character_symbol [a] χ).2.1
  change bruhatOrbitDeriv a (fun x ↦ (χ x : ℂ)) 1 =
    (((characterSlope a χ).toAdd : ℝ) : ℂ) * Complex.I * 1 at h
  change (bruhatOrbitDeriv a (fun x ↦ (χ x : ℂ)) 1).im / (2 * Real.pi) = _
  rw [h]
  simp [Complex.mul_im]

private theorem bruhatReadFrequency_pairing (a : Multiplicative ℝ →ₜ* G)
    (χ : PontryaginDual G) (t : ℝ) :
    Circle.exp (2 * Real.pi * (bruhatReadFrequency (bruhatFirstOrder a) χ * t)) =
      χ (a (Multiplicative.ofAdd t)) := by
  rw [bruhatReadFrequency_firstOrder]
  calc
    _ = Circle.exp ((characterSlope a χ).toAdd * t) := by
      congr 1
      have h : (2 * Real.pi) ≠ 0 := by positivity
      field_simp
    _ = _ := (characterSlope_eq_exp a (χ : CircleCharacter G) t).symm

private theorem bruhatReadFrequency_mem (D : bruhatFirstOrderReal (G := G)) :
    bruhatReadFrequency D.val ∈ continuousRealHomSubmodule (PontryaginDual G) := by
  obtain ⟨a, ha⟩ := bruhatFirstOrderReal_represent D
  change Continuous (bruhatReadFrequency D.val) ∧
    ∀ x y, bruhatReadFrequency D.val (x * y) = _
  rw [ha]
  let v : CircleCharacter G →* Multiplicative ℝ := characterSlope a
  have he : bruhatReadFrequency (bruhatFirstOrder a) =
      fun χ : PontryaginDual G ↦ (v (χ : CircleCharacter G)).toAdd / (2 * Real.pi) :=
    funext (bruhatReadFrequency_firstOrder a)
  rw [he]
  refine ⟨((continuous_toAdd.comp (characterSlope_continuous a)).div_const _), fun x y ↦ ?_⟩
  change (v ((x : CircleCharacter G) * (y : CircleCharacter G))).toAdd / (2 * Real.pi) =
    (v (x : CircleCharacter G)).toAdd / (2 * Real.pi) +
      (v (y : CircleCharacter G)).toAdd / (2 * Real.pi)
  exact (congrArg (fun z : Multiplicative ℝ ↦ z.toAdd / (2 * Real.pi))
    (map_mul v (x : CircleCharacter G) (y : CircleCharacter G))).trans (add_div _ _ _)

private def realFourierPairing (u : ℝ) : PontryaginDual (Multiplicative ℝ) where
  toFun v := Circle.exp (2 * Real.pi * (u * v.toAdd))
  map_one' := by change Circle.exp (2 * Real.pi * (u * 0)) = 1; simp
  map_mul' v w := by
    change Circle.exp (2 * Real.pi * (u * (v.toAdd + w.toAdd))) = _
    rw [mul_add, mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp
    (continuous_const.mul (continuous_const.mul continuous_toAdd))

private theorem realFourierPairing_continuous : Continuous realFourierPairing :=
  ContinuousMonoidHom.continuous_of_continuous_uncurry realFourierPairing
    (Circle.exp.continuous.comp (continuous_const.mul
      (continuous_fst.mul (continuous_toAdd.comp continuous_snd))))

/-- Lemma D.1.6.14. The normalized frequency is a real-linear isomorphism
and agrees with the canonical dual pairing of one-parameter subgroups. -/
theorem bruhatFirstOrder_frequency :
    ∃ σ : bruhatFirstOrderReal (G := G) ≃ₗ[ℝ] continuousRealHomSubmodule (PontryaginDual G),
      ∀ (a : Multiplicative ℝ →ₜ* G) (D : bruhatFirstOrderReal (G := G)),
        D.val = bruhatFirstOrder a → ∀ (χ : PontryaginDual G) (t : ℝ),
          Circle.exp (2 * Real.pi * ((σ D).val χ * t)) = χ (a (Multiplicative.ofAdd t)) := by
  let L := (bruhatReadFrequency.comp (bruhatFirstOrderReal (G := G)).subtype).codRestrict
    (continuousRealHomSubmodule (PontryaginDual G)) bruhatReadFrequency_mem
  have hinj : Injective L := by
    intro D E he
    obtain ⟨a, ha⟩ := bruhatFirstOrderReal_represent D
    obtain ⟨b, hb⟩ := bruhatFirstOrderReal_represent E
    have hχ (χ : PontryaginDual G) :
        bruhatReadFrequency (bruhatFirstOrder a) χ =
          bruhatReadFrequency (bruhatFirstOrder b) χ := by
      rw [← ha, ← hb]
      exact congrArg (fun u : continuousRealHomSubmodule (PontryaginDual G) ↦ u.val χ) he
    have heq : a = b := by
      apply ContinuousMonoidHom.ext
      intro t
      apply pontryaginBidualEval_isClosedEmbedding.injective
      apply PontryaginDual.ext
      intro χ
      change χ (a (Multiplicative.ofAdd t.toAdd)) = χ (b (Multiplicative.ofAdd t.toAdd))
      rw [← bruhatReadFrequency_pairing a, ← bruhatReadFrequency_pairing b, hχ]
    apply Subtype.ext
    rw [ha, hb, heq]
  have hsurj : Surjective L := by
    intro h
    obtain ⟨e, he⟩ := oneParameterSubgroups_dual (G := G)
    have hprop : Continuous h.val ∧ ∀ x y, h.val (x * y) = h.val x + h.val y := h.property
    have hzero : h.val 1 = 0 := by
      have hh := hprop.2 1 1
      rw [one_mul] at hh
      linarith
    let k : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ) :=
      { toFun := fun χ ↦ realFourierPairing (h.val χ)
        map_one' := PontryaginDual.ext fun t ↦ by
          change Circle.exp (2 * Real.pi * (h.val 1 * t.toAdd)) = 1
          simp [hzero]
        map_mul' := fun χ ψ ↦ PontryaginDual.ext fun t ↦ by
          change Circle.exp (2 * Real.pi * (h.val (χ * ψ) * t.toAdd)) = _
          rw [hprop.2, add_mul, mul_add, Circle.exp_add]
          rfl
        continuous_toFun := realFourierPairing_continuous.comp hprop.1 }
    obtain ⟨a, ha⟩ := e.surjective k
    rw [he] at ha
    refine ⟨⟨bruhatFirstOrder a, Submodule.subset_span ⟨a, rfl⟩⟩, Subtype.ext (funext fun χ ↦ ?_)⟩
    have hfreq := characterSlope_unique a χ (2 * Real.pi * h.val χ) (fun t ↦ by
      have hh := congrArg (fun u : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ) ↦
        u χ (Multiplicative.ofAdd t)) ha
      change χ (a (Multiplicative.ofAdd t)) = Circle.exp (2 * Real.pi * (h.val χ * t)) at hh
      change χ (a (Multiplicative.ofAdd t)) =
        Circle.exp ((2 * Real.pi * h.val χ) * t)
      rw [mul_assoc]
      exact hh)
    change bruhatReadFrequency (bruhatFirstOrder a) χ = h.val χ
    rw [bruhatReadFrequency_firstOrder, hfreq]
    have hn : (2 * Real.pi) ≠ 0 := by positivity
    exact mul_div_cancel_left₀ _ hn
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun a D ha χ t ↦ ?_⟩
  change Circle.exp (2 * Real.pi * (bruhatReadFrequency D.val χ * t)) = _
  rw [ha, bruhatReadFrequency_pairing]

end

end Masullo
