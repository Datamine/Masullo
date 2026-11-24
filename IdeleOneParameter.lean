import Ideles
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Instances.RealVectorSpace

open Function IsDedekindDomain NumberField Set Topology
open scoped ContDiff NumberField RestrictedProduct

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

private noncomputable def finiteIdelePart : Idele F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map
    { toFun := Prod.snd
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- The closed infinite-place subgroup inside the ideles. The finite
component of each of its elements is the identity. -/
noncomputable def infinitePlaceIdeles : Subgroup (Idele F) :=
  (finiteIdelePart F).ker

private theorem mem_infinitePlaceIdeles_iff (g : Idele F) :
    g ∈ infinitePlaceIdeles F ↔ ∀ v : HeightOneSpectrum (𝓞 F), g.val.2 v = 1 := by
  change finiteIdelePart F g = 1 ↔ _
  constructor
  · intro h v
    exact congrArg (fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => u.val v) h
  · intro h
    apply Units.ext
    change g.val.2 = 1
    exact RestrictedProduct.ext _ _ h

/-- Membership in the infinite-place subgroup means the entire finite component is one. -/
theorem finite_component_eq_one_of_mem_infinitePlaceIdeles {g : Idele F}
    (hg : g ∈ infinitePlaceIdeles F) : g.val.2 = 1 :=
  RestrictedProduct.ext _ _ ((mem_infinitePlaceIdeles_iff F g).mp hg)

private theorem continuous_finiteIdeleCoord (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun g : Idele F => g.val.2 v) := by
  have h : Continuous (fun g : Idele F => g.val.2) :=
    continuous_snd.comp (Units.continuous_val (M := NumberField.AdeleRing (𝓞 F) F))
  exact (RestrictedProduct.continuous_eval v).comp h

theorem infinitePlaceIdeles_isClosed : IsClosed (infinitePlaceIdeles F : Set (Idele F)) := by
  have he : (infinitePlaceIdeles F : Set (Idele F)) =
      ⋂ v : HeightOneSpectrum (𝓞 F), (fun g : Idele F => g.val.2 v) ⁻¹' {1} := by
    ext g
    simpa only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] using
      mem_infinitePlaceIdeles_iff F g
  rw [he]
  exact isClosed_iInter fun v => isClosed_singleton.preimage (continuous_finiteIdeleCoord F v)

private theorem idele_oneParameter_finite (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    ∀ t, γ t ∈ infinitePlaceIdeles F := by
  intro t
  apply (mem_infinitePlaceIdeles_iff F (γ t)).mpr
  intro v
  let p (s : ℝ) : v.adicCompletion F := (γ (Multiplicative.ofAdd s)).val.2 v
  have hp : Continuous p :=
    (continuous_finiteIdeleCoord F v).comp (hγ.comp continuous_ofAdd)
  have h : (γ t).val.2 v = (γ (1 : Multiplicative ℝ)).val.2 v :=
    TotallyDisconnectedSpace.eq_of_continuous p hp (Multiplicative.toAdd t) 0
  rw [h, map_one]
  rfl

theorem idele_oneParameter_logNorm (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    ∃ a : ℝ, ∀ t : ℝ, Real.log (ideleNorm F (γ (Multiplicative.ofAdd t))) = t * a := by
  let φ : ℝ →+ ℝ :=
    { toFun := fun t => Multiplicative.toAdd ((ideleLogNorm F) (γ (Multiplicative.ofAdd t)))
      map_zero' := by simp
      map_add' := by intro x y; simp }
  have hφ : Continuous φ :=
    continuous_toAdd.comp ((ideleLogNorm_continuous F).comp (hγ.comp continuous_ofAdd))
  let e := φ.toRealLinearMap hφ
  refine ⟨e 1, fun t => ?_⟩
  change e t = t * e 1
  simpa [smul_eq_mul] using e.map_smul t (1 : ℝ)

/-- The two cases of Lemma 2.2.4.1 in the logarithmic parametrization. In
the nonconstant case the modulus is a smooth power automorphism, with
inverse given by the reciprocal exponent. -/
theorem idele_oneParameter_structure
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    (∀ t, γ t ∈ infinitePlaceIdeles F) ∧
      ((∀ t, ideleNorm F (γ t) = 1) ∨
        ∃! a : ℝ, a ≠ 0 ∧
          (∀ t : ℝ, ideleNorm F (γ (Multiplicative.ofAdd t)) = Real.exp t ^ a) ∧
          (∃ t, ideleNorm F (γ t) ≠ 1) ∧
          ContDiffOn ℝ ∞ (fun x : ℝ => x ^ a) (Ioi (0 : ℝ)) ∧
          ContDiffOn ℝ ∞ (fun x : ℝ => x ^ a⁻¹) (Ioi (0 : ℝ)) ∧
          MapsTo (fun x : ℝ => x ^ a) (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) ∧
          MapsTo (fun x : ℝ => x ^ a⁻¹) (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) ∧
          LeftInvOn (fun x : ℝ => x ^ a⁻¹) (fun x : ℝ => x ^ a) (Ioi (0 : ℝ)) ∧
          RightInvOn (fun x : ℝ => x ^ a⁻¹) (fun x : ℝ => x ^ a) (Ioi (0 : ℝ))) := by
  refine ⟨idele_oneParameter_finite F γ hγ, ?_⟩
  obtain ⟨a, ha⟩ := idele_oneParameter_logNorm F γ hγ
  have he (t : ℝ) : ideleNorm F (γ (Multiplicative.ofAdd t)) = Real.exp t ^ a := by
    rw [← Real.exp_log (ideleNorm_pos F _), ha, Real.exp_mul]
  by_cases hzero : a = 0
  · exact Or.inl fun t => by simpa [hzero] using he (Multiplicative.toAdd t)
  · refine Or.inr ⟨a, ⟨hzero, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · refine ⟨Multiplicative.ofAdd 1, ?_⟩
      rw [he, ← Real.exp_mul, one_mul]
      exact fun h => hzero (Real.exp_injective (h.trans Real.exp_zero.symm))
    · exact fun x hx => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp hx).ne').contDiffWithinAt
    · exact fun x hx => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp hx).ne').contDiffWithinAt
    · exact fun _ hx => Real.rpow_pos_of_pos (mem_Ioi.mp hx) _
    · exact fun _ hx => Real.rpow_pos_of_pos (mem_Ioi.mp hx) _
    · intro x hx
      change (x ^ a) ^ a⁻¹ = x
      rw [← Real.rpow_mul (mem_Ioi.mp hx).le, mul_inv_cancel₀ hzero, Real.rpow_one]
    · intro x hx
      change (x ^ a⁻¹) ^ a = x
      rw [← Real.rpow_mul (mem_Ioi.mp hx).le, inv_mul_cancel₀ hzero, Real.rpow_one]
    · intro b hb
      have hab := (hb.2.1 1).symm.trans (he 1)
      rw [← Real.exp_mul, ← Real.exp_mul, one_mul, one_mul] at hab
      exact Real.exp_injective hab

end Masullo
