import SLocalPairedMellin
import SLocalPaleyWienerLevels

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev G := (SAdeles F S)ˣ
private abbrev K := SLocalThetaNormOne F S
private abbrev L := SIdeleQuotient F S

private theorem globalBruhat_translate_comp (g h : Idele F) (f : GlobalBruhat F) :
    GlobalBruhat.leftTranslate F g (GlobalBruhat.leftTranslate F h f) =
      GlobalBruhat.leftTranslate F (g * h) f := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F g
    (GlobalBruhat.leftTranslate F h f)) =
      GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F (g*h) f)
  rw [GlobalBruhat.leftTranslate_apply, GlobalBruhat.leftTranslate_apply,
    GlobalBruhat.leftTranslate_apply, mul_inv_rev, Units.val_mul, mul_assoc]

private theorem globalBruhat_translate_one (f : GlobalBruhat F) :
    GlobalBruhat.leftTranslate F 1 f = f := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F 1 f) =
    GlobalBruhat.evaluation F x f
  rw [GlobalBruhat.leftTranslate_apply, inv_one, Units.val_one, one_mul]

/-- The selected local Fourier integral has the usual modulus under
dilation, on every stage with its actual Tamagawa normalization. -/
theorem sLocalSelectedFourier_leftTranslate (g : G F S) (f : E F S) :
    sLocalSelectedFourier F S (sLocalBruhatLeftTranslate F S g f) =
      (sLocalIdeleNorm F S g : ℂ) •
        sLocalBruhatLeftTranslate F S g⁻¹ (sLocalSelectedFourier F S f) := by
  let b := (sLocalEmbed F S g).val
  let a := sLocalCodifferentTailIdele F S
  let T := sLocalFourierCompression F S
  have hb : (sLocalEmbed F S g⁻¹).val = b⁻¹ := by simp [b]
  have h : GlobalBruhat.leftTranslate F a (T (sLocalBruhatLeftTranslate F S g f)).val =
      (sLocalIdeleNorm F S g : ℂ) •
        GlobalBruhat.leftTranslate F b⁻¹ (GlobalBruhat.leftTranslate F a (T f).val) := by
    rw [← sLocalFourier_eq_tailTranslate, ← sLocalFourier_eq_tailTranslate]
    exact globalBruhat_fourier_leftTranslate F b f.val
  have he := congrArg (GlobalBruhat.leftTranslate F a⁻¹) h
  rw [map_smul, globalBruhat_translate_comp, inv_mul_cancel, globalBruhat_translate_one,
    globalBruhat_translate_comp, globalBruhat_translate_comp] at he
  have hab : a⁻¹ * b⁻¹ * a = b⁻¹ := by
    rw [mul_comm a⁻¹ b⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  rw [hab] at he
  have hu : T (sLocalBruhatLeftTranslate F S g f) =
      (sLocalIdeleNorm F S g : ℂ) • sLocalBruhatLeftTranslate F S g⁻¹ (T f) := by
    apply Subtype.ext
    change _ = (sLocalIdeleNorm F S g : ℂ) •
      GlobalBruhat.leftTranslate F (sLocalEmbed F S g⁻¹).val (T f).val
    rw [hb]
    exact he
  unfold sLocalSelectedFourier
  simp only [smul_apply, map_smul]
  change _ • T (sLocalBruhatLeftTranslate F S g f) = _
  rw [hu, smul_comm]

theorem sLocalZetaWeight_inverse_argument (ω : PontryaginDual (K F S)) (z : ℂ) (q : L F S) :
    sLocalZetaWeight F S ω z q⁻¹ = (sLocalZetaWeight F S ω z q)⁻¹ := by
  have h1 : sLocalZetaWeight F S ω z 1 = 1 := by
    have he : sLocalZetaSplit F S (0, 1) = 1 := by
      change (QuotientGroup.mk' (sUnitImage F S)) ((sLocalExpSection F S) 1) * 1 = 1
      rw [map_one, map_one]
      exact one_mul (1 : L F S)
    rw [← he, sLocalZetaWeight_split]
    simp
  have he := sLocalZetaWeight_mul F S ω z q q⁻¹
  rw [mul_inv_cancel, h1] at he
  by_cases hn : sLocalZetaWeight F S ω z q = 0
  · simp [hn] at he
  · apply mul_left_cancel₀ hn
    exact he.symm.trans (mul_inv_cancel₀ hn).symm

/-- The modulus from Fourier cancels the reflected dilation weight. -/
theorem sLocalZetaWeight_reflected_dilation (ω : PontryaginDual (K F S)) (z : ℂ) (q : L F S) :
    (sLocalClassModulus F S q : ℂ) * sLocalZetaWeight F S ω⁻¹ (1-z) q⁻¹ =
      sLocalZetaWeight F S ω z q := by
  rw [sLocalZetaWeight_inverse_argument]
  obtain ⟨⟨t,k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
  have ht : sLocalClassModulus F S (sLocalZetaSplit F S (t,k)) = Real.exp t := by
    have hlog := sLocalZetaSplit_logModulus F S (t,k)
    change Real.log (sLocalClassModulus F S (sLocalZetaSplit F S (t,k))) = t at hlog
    exact (Real.exp_log (sLocalClassModulus_pos F S _)).symm.trans (congrArg Real.exp hlog)
  rw [ht, sLocalZetaWeight_split, sLocalZetaWeight_split, Complex.ofReal_exp,
    mul_inv, ← Complex.exp_neg]
  have hk : (((ω⁻¹ k : Circle) : ℂ)⁻¹) = (ω k : ℂ) := by
    change (((ω k)⁻¹ : Circle) : ℂ)⁻¹ = _
    rw [Circle.coe_inv, inv_inv]
  rw [hk, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable (ν : Measure (K F S)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F S))
variable (μ : Measure (G F S)) [μ.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S) μ Measure.count (sLocalClassHaar F S ν))

include μ hν in
/-- Both components of the paired transform acquire the same character
weight under translation. The equality holds on their respective half-planes. -/
theorem sLocalPairedBergmanMellin_translate
    (g : G F S) (q : SLocalHomogeneousThetaQuotient F S ν ω) :
    let q' := sLocalHomogeneousThetaTranslate F S ν ω (QuotientGroup.mk g) q
    (∀ z, 0 < z.re →
      (sLocalPairedBergmanMellin F S ν ω q').1.val z =
        sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
          (sLocalPairedBergmanMellin F S ν ω q).1.val z) ∧
    (∀ z, z.re < 1 →
      (sLocalPairedBergmanMellin F S ν ω q').2.val z =
        sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
          (sLocalPairedBergmanMellin F S ν ω q).2.val z) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (sLocalHomogeneousThetaKernel F S ν ω) q
  have ht : sLocalHomogeneousThetaTranslate F S ν ω (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S g f) :=
    sLocalHomogeneousThetaTranslate_mkQ F S ν ω g f
  dsimp only
  rw [ht]
  obtain ⟨h₁, h₂⟩ := sLocalPairedBergmanMellin_idelic F S ν ω μ hν f
  obtain ⟨h₁', h₂'⟩ := sLocalPairedBergmanMellin_idelic F S ν ω μ hν
    (sLocalBruhatLeftTranslate F S g f)
  constructor
  · intro z hz
    rw [h₁ z hz, h₁' z hz, sLocalIdelicZetaIntegral_leftTranslate]
  · intro z hz
    rw [h₂ z hz, h₂' z hz, sLocalSelectedFourier_leftTranslate]
    have hp : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hz
    obtain ⟨hB, _⟩ := sLocalPairedBergmanMellin_idelic F S ν ω⁻¹ μ hν
      (sLocalBruhatLeftTranslate F S g⁻¹ (sLocalSelectedFourier F S f))
    let c : ℂ := (sLocalIdeleNorm F S g : ℂ)
    let u := sLocalBruhatLeftTranslate F S g⁻¹ (sLocalSelectedFourier F S f)
    have hlin : sLocalIdelicZetaIntegral F S μ ω⁻¹ (c • u) (1-z) =
        c * sLocalIdelicZetaIntegral F S μ ω⁻¹ u (1-z) := by
      rw [← hB (1-z) hp]
      have he := (sLocalPairedBergmanMellin_idelic F S ν ω⁻¹ μ hν (c • u)).1 (1-z) hp
      rw [← he]
      change (sLocalPairedBergmanMellin F S ν ω⁻¹
          ((sLocalHomogeneousThetaKernel F S ν ω⁻¹).mkQ (c • u))).1.val (1-z) = _
      rw [map_smul, map_smul]
      rfl
    change sLocalIdelicZetaIntegral F S μ ω⁻¹ (c • u) (1-z) = _
    rw [hlin, sLocalIdelicZetaIntegral_leftTranslate, ← mul_assoc]
    have hc : c = (sLocalClassModulus F S (QuotientGroup.mk g) : ℂ) := rfl
    rw [hc, show (QuotientGroup.mk g⁻¹ : L F S) = (QuotientGroup.mk g)⁻¹ from
      map_inv (QuotientGroup.mk' (sUnitImage F S)) g, sLocalZetaWeight_reflected_dilation]

/-- At spectral exponent zero and logarithmic modulus one, the printed
reflected multiplier differs from the verified one. -/
theorem sLocalPairedMellin_printed_left_weight_ne :
    let q := sLocalZetaSplit F S (1, (1 : K F S))
    sLocalZetaWeight F S 1 0 q ≠ sLocalZetaWeight F S 1 (1-0) q := by
  dsimp only
  rw [sLocalZetaWeight_split, sLocalZetaWeight_split]
  simp only [sub_zero, Complex.ofReal_one, mul_one, Complex.exp_zero,
    map_one, Circle.coe_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ne_eq, Complex.ofReal_inj]
  exact ne_of_lt (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr zero_lt_one : 1 < Real.exp 1)

end

end Masullo
