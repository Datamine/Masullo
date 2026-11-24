import IdelicFundamentalDomain
import ArchimedeanOrbitalProducts

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- Give an Archimedean idele trivial finite component. -/
def archIntoIdeles : InfiniteIdeles F →* Idele F :=
  MulEquiv.prodUnits.symm.toMonoidHom.comp
    ((MonoidHom.id (InfiniteIdeles F)).prod (1 : InfiniteIdeles F →* (FiniteAdeleRing (𝓞 F) F)ˣ))

theorem archIntoIdeles_continuous : Continuous (archIntoIdeles F) :=
  (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

theorem archIntoIdeles_logNorm (a : InfiniteIdeles F) :
    ideleLogNorm F (archIntoIdeles F a) = infiniteIdeleLogNorm F a := by
  rw [infiniteIdeleLogNorm_eq]
  have ha : archIntoIdeles F a ∈ (ideleDivisor F).ker := by
    apply (ideleDivisor_ker_iff_prodUnits F _).mpr
    change (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) ∈ (finiteIntegralSubmonoid F).units
    exact (finiteIntegralSubmonoid F).units.one_mem
  change Multiplicative.ofAdd (Real.log (ideleNorm F (archIntoIdeles F a))) = _
  rw [ideleNorm_eq_arch_of_finite_integral F _ ha]
  rfl

private theorem ideleLogNorm_one_iff (a : Idele F) :
    ideleLogNorm F a = 1 ↔ ideleNorm F a = 1 := by
  change Real.log (ideleNorm F a) = 0 ↔ _
  constructor
  · intro h
    rw [← Real.exp_log (ideleNorm_pos F a), h, Real.exp_zero]
  · rintro h
    rw [h, Real.log_one]

/-- Lemma A.2.3.12. Every idele has unique principal, positive modulus,
and fundamental-domain coordinates, for any Archimedean homomorphic section. -/
theorem ideleOrbitalProduct_bijective (v : InfinitePlace F)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F)
    (hg : ∀ c, normOneIdealClass F (g c) = c)
    (s : Multiplicative ℝ →* InfiniteIdeles F)
    (hs : ∀ t, infiniteIdeleLogNorm F (s t) = t) :
    Bijective (fun p : Fˣ × Multiplicative ℝ × ideleFundamentalDomain F v g =>
      principalIdele F p.1 * archIntoIdeles F (s p.2.1) * p.2.2.val.val) := by
  let S := (archIntoIdeles F).comp s
  have hS (t : Multiplicative ℝ) : ideleLogNorm F (S t) = t := by
    change ideleLogNorm F (archIntoIdeles F (s t)) = t
    rw [archIntoIdeles_logNorm, hs]
  have hp (t : Fˣ) : ideleLogNorm F (principalIdele F t) = 1 :=
    (ideleLogNorm_one_iff F _).mpr (ideleNorm_principal F t)
  have hx (x : NormOneIdeles F) : ideleLogNorm F x.val = 1 :=
    (ideleLogNorm_one_iff F _).mpr x.property
  have hcoord (t : Fˣ) (r : Multiplicative ℝ) (x : NormOneIdeles F) :
      ideleLogNorm F (principalIdele F t * S r * x.val) = r := by
    rw [map_mul, map_mul, hp, hS, hx, one_mul, mul_one]
  constructor
  · rintro ⟨t, r, x⟩ ⟨u, q, y⟩ h
    change principalIdele F t * S r * x.val.val = principalIdele F u * S q * y.val.val at h
    have hrq : r = q := (hcoord t r x.val).symm.trans
      ((congrArg (ideleLogNorm F) h).trans (hcoord u q y.val))
    subst q
    have he : principalNormOne F t * x.val = principalNormOne F u * y.val := by
      apply Subtype.ext
      change principalIdele F t * x.val.val = principalIdele F u * y.val.val
      rw [mul_right_comm (principalIdele F t), mul_right_comm (principalIdele F u)] at h
      exact mul_right_cancel h
    have hy : principalNormOne F (t / u) * x.val = y.val := by
      rw [map_div, div_eq_mul_inv, mul_comm (principalNormOne F t), mul_assoc, he, inv_mul_cancel_left]
    obtain ⟨w, _, hw⟩ := ideleFundamentalDomain_unique F v g hg x.val
    have hw₀ : principalNormOne F 1 * x.val ∈ ideleFundamentalDomain F v g := by
      rw [map_one, one_mul]
      exact x.property
    have hw₁ : principalNormOne F (t / u) * x.val ∈ ideleFundamentalDomain F v g := by
      rw [hy]
      exact y.property
    have htu : t = u := div_eq_one.mp ((hw (t / u) hw₁).trans (hw 1 hw₀).symm)
    subst u
    have hxy : x.val = y.val := mul_left_cancel he
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext hxy))
  · intro a
    let r := ideleLogNorm F a
    let x : NormOneIdeles F := ⟨a / S r, (ideleLogNorm_one_iff F _).mp (by
      rw [map_div, hS]
      exact div_self' r)⟩
    obtain ⟨u, hu, _⟩ := ideleFundamentalDomain_unique F v g hg x
    refine ⟨(u⁻¹, r, ⟨principalNormOne F u * x, hu⟩), ?_⟩
    change principalIdele F u⁻¹ * S r * (principalIdele F u * (a / S r)) = a
    rw [map_inv, ← mul_assoc, mul_right_comm ((principalIdele F u)⁻¹) (S r),
      inv_mul_cancel, one_mul, mul_comm (S r), div_mul_cancel]

end

end Masullo
