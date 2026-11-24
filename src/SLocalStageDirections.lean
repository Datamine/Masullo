import IdelicSubgroupDirections
import IdelicStageCofinalBasis
import SUnitRank

open Function IsDedekindDomain NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Arch" => mixedEmbedding.mixedSpace F

/-- The open S-local inclusion as a continuous homomorphism. -/
def sIdeleClassContinuousInclusion : SIdeleClass F S →ₜ* IdeleClass F :=
  ⟨sIdeleClassInclusion F S, (sIdeleClassInclusion_openEmbedding F S).continuous⟩

/-- The S-local norm in the logarithmic parameter. -/
def sIdeleClassLogModulation : SIdeleClass F S →ₜ* Multiplicative ℝ :=
  (⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩ : IdeleClass F →ₜ* Multiplicative ℝ).comp
    (sIdeleClassContinuousInclusion F S)

theorem sIdeleClassLogModulation_ker :
    (sIdeleClassLogModulation F S).toMonoidHom.ker = sNormOneClass F S := by
  change ((ideleClassLogNorm F).ker).comap (sIdeleClassInclusion F S) = _
  rw [ideleClassLogNorm_ker_eq_normOne]
  rfl

theorem sIdeleClassLogModulation_proper :
    IsProperMap (sIdeleClassLogModulation F S) := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ := ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have ho := sIdeleClassInclusion_openEmbedding F S
  have hc : IsClosed (Set.range (sIdeleClassInclusion F S)) :=
    (sIdeleClassInclusion F S).range.isClosed_of_isOpen ho.isOpen_range
  exact hm.comp (show IsClosedEmbedding (sIdeleClassInclusion F S) from
    ⟨ho.isEmbedding, hc⟩).isProperMap

/-- The archimedean directions lie in each S-local idele class group and
parametrize all its real directions faithfully. -/
theorem exists_sIdeleClass_directionParametrization :
    ∃ e : Multiplicative Arch →ₜ* SIdeleClass F S,
      (∀ x, sIdeleClassInclusion F S (e x) = archimedeanClassExponential F x) ∧
      (∀ c : Multiplicative ℝ →ₜ* SIdeleClass F S, ∃ x : Arch, ∀ t : ℝ,
        c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x))) ∧
      (∀ x : Arch, (∀ t : ℝ, e (Multiplicative.ofAdd (t • x)) = 1) → x = 0) := by
  let i := sIdeleClassContinuousInclusion F S
  have hi : IsEmbedding i := (sIdeleClassInclusion_openEmbedding F S).isEmbedding
  have h (x : Multiplicative Arch) : archimedeanClassExponential F x ∈ Set.range i := by
    have hx : archimedeanClassExponential F x ∈
        (sIdeleClassInclusion F S) '' connectedComponent 1 := by
      rw [sIdeleClass_identityComponent]
      exact archimedeanClassExponential_mem_identityComponent F x
    obtain ⟨y, _, hy⟩ := hx
    exact ⟨y, hy⟩
  exact @exists_idelic_subgroupDirectionParametrization F _ _ (SIdeleClass F S) _ _ i hi h

/-- Every global one-parameter subgroup, including a prescribed radial
section, has a compatible lift to every S-local class group. -/
theorem exists_sIdeleClass_lift_oneParameter (c : Multiplicative ℝ →ₜ* IdeleClass F) :
    ∃ b : Multiplicative ℝ →ₜ* SIdeleClass F S,
      ∀ t, sIdeleClassInclusion F S (b t) = c t := by
  let i := sIdeleClassContinuousInclusion F S
  have h (t : Multiplicative ℝ) : c t ∈ Set.range i := by
    have ht : c t ∈ (sIdeleClassInclusion F S) '' connectedComponent 1 := by
      rw [sIdeleClass_identityComponent]
      exact oneParameter_mem_identityComponent c t
    obtain ⟨y, _, hy⟩ := ht
    exact ⟨y, hy⟩
  exact @exists_continuousHom_factor_embedding (Multiplicative ℝ) (SIdeleClass F S) (IdeleClass F)
    _ _ _ _ _ _ i (sIdeleClassInclusion_openEmbedding F S).isEmbedding c h

/-- Once the S-local group meets all ideal classes, its inclusion is a
topological group isomorphism onto the global idele class group. -/
def sIdeleClassContinuousEquiv (hs : Surjective (sIdeleClassInclusion F S)) :
    SIdeleClass F S ≃ₜ* IdeleClass F :=
  ContinuousMulEquiv.mk'
    ((sIdeleClassInclusion_openEmbedding F S).isEmbedding.toHomeomorphOfSurjective hs)
    (map_mul (sIdeleClassInclusion F S))

@[simp] theorem sIdeleClassContinuousEquiv_apply
    (hs : Surjective (sIdeleClassInclusion F S)) (x : SIdeleClass F S) :
    sIdeleClassContinuousEquiv F S hs x = sIdeleClassInclusion F S x := rfl

/-- The eventual identification preserves the logarithmic modulus. -/
theorem exists_sIdeleClass_eventualContinuousEquiv :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, S₀ ⊆ T →
      ∃ e : SIdeleClass F T ≃ₜ* IdeleClass F,
        (∀ x, e x = sIdeleClassInclusion F T x) ∧
        ∀ x, ideleClassLogNorm F (e x) = sIdeleClassLogModulation F T x := by
  obtain ⟨S₀, hS₀⟩ := sIdeleClass_eventually_surjective F
  exact ⟨S₀, fun T hT =>
    ⟨sIdeleClassContinuousEquiv F T (hS₀ T hT), fun _ => rfl, fun _ => rfl⟩⟩

end
end Masullo
