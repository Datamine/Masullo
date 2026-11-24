import Ideles
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Filter IsDedekindDomain NumberField Set
open scoped NumberField SchwartzMap Classical

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

abbrev Adeles := NumberField.AdeleRing (𝓞 F) F

/-- The additive finite-place input to a pure Schwartz–Bruhat tensor. -/
structure FiniteBruhat where
  toLocallyConstant : LocallyConstant (FiniteAdeleRing (𝓞 F) F) ℂ
  compactSupport : HasCompactSupport toLocallyConstant

/-- A pure adelic Schwartz–Bruhat tensor, using the mixed archimedean model. -/
def bruhatTensor (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F) :
    Adeles F → ℂ :=
  fun a => φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * ψ.toLocallyConstant a.2

/-- Algebraic space of finite sums of global Schwartz–Bruhat tensors.
Its locally convex topology is a separate construction. -/
def bruhatSubmodule : Submodule ℂ (Adeles F → ℂ) :=
  Submodule.span ℂ {f | ∃ φ ψ, bruhatTensor F φ ψ = f}

theorem bruhatTensor_mem (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F) :
    bruhatTensor F φ ψ ∈ bruhatSubmodule F :=
  Submodule.subset_span ⟨φ, ψ, rfl⟩

omit [NumberField F] in
theorem infiniteAdele_toMixed_continuous :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous (fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x)
  simp_rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.property).continuous.comp
      (continuous_apply v.val)
  · apply continuous_pi
    intro v
    exact (InfinitePlace.Completion.isometry_extensionEmbedding v.val).continuous.comp
      (continuous_apply v.val)

/-- The pure generators are continuous for the adelic ring topology. -/
theorem bruhatTensor_continuous (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F) :
    Continuous (bruhatTensor F φ ψ) := by
  have hinf : Continuous (fun a : Adeles F => a.1) := continuous_fst
  have hfin : Continuous (fun a : Adeles F => a.2) := continuous_snd
  have harch := infiniteAdele_toMixed_continuous F
  exact (φ.continuous.comp (harch.comp hinf)).mul (ψ.toLocallyConstant.continuous.comp hfin)

theorem bruhat_continuous {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Continuous f := by
  apply Submodule.span_induction (p := fun f _ => Continuous f) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    exact bruhatTensor_continuous F φ ψ
  · exact continuous_const
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro c f _ hf
    exact hf.const_smul c

/-- A Schwartz function is absolutely summable over any translate of a
discrete lattice. This discharges the archimedean summability step once the
finite-place support restricts the adelic sum to a lattice. -/
theorem schwartz_summable_on_lattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (φ : 𝓢(E, ℂ)) (x : E) : Summable (fun l : L => ‖φ ((l : E) - x)‖) := by
  let k := Module.finrank ℤ L + 1
  have hsum := (ZLattice.summable_norm_sub_inv_pow L k (Nat.lt_succ_self _) x).mul_left
    (SchwartzMap.seminorm ℝ k 0 φ)
  apply hsum.of_norm_bounded_eventually
  have hne : ∀ᶠ l : L in cofinite, (l : E) - x ≠ 0 := by
    by_cases hx : x ∈ L
    · filter_upwards [eventually_cofinite_ne (⟨x, hx⟩ : L)] with l hl
      exact sub_ne_zero.mpr fun h => hl (Subtype.ext h)
    · exact Eventually.of_forall fun l => sub_ne_zero.mpr fun h => hx (h ▸ l.property)
  filter_upwards [hne] with l hl
  rw [Real.norm_of_nonneg (norm_nonneg _), inv_pow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hl) _)).mpr
  rw [mul_comm]
  exact SchwartzMap.norm_pow_mul_le_seminorm ℝ φ k _

/-- The summands in (2.2.3.1), indexed by nonzero field elements. -/
def thetaSummand (f : Adeles F → ℂ) (g : Idele F) (ξ : Fˣ) : ℂ :=
  f ((principalIdele F ξ * g).val)

/-- Convergence of the series in Definition 2.2.3.1. -/
def thetaSummable (f : Adeles F → ℂ) : Prop :=
  ∀ g : Idele F, Summable (thetaSummand F f g)

def thetaOnIdeles (f : Adeles F → ℂ) (g : Idele F) : ℂ :=
  ∑' ξ : Fˣ, thetaSummand F f g ξ

theorem thetaOnIdeles_principal_mul (f : Adeles F → ℂ) (g : Idele F) (a : Fˣ) :
    thetaOnIdeles F f (principalIdele F a * g) = thetaOnIdeles F f g := by
  unfold thetaOnIdeles
  simpa only [thetaSummand, Equiv.coe_mulRight, map_mul, mul_assoc] using
    (Equiv.mulRight a).tsum_eq (thetaSummand F f g)

/-- Descent of the nonzero theta sum to the idele class group. -/
def adelicTheta (f : Adeles F → ℂ) : IdeleClass F → ℂ :=
  Quotient.lift (thetaOnIdeles F f) fun x y h => by
    change (QuotientGroup.leftRel (principalIdeles F)).r x y at h
    rw [QuotientGroup.leftRel_apply] at h
    obtain ⟨a, ha⟩ := h
    have hy : y = principalIdele F a * x := by rw [ha, mul_comm (x⁻¹ * y), mul_inv_cancel_left]
    rw [hy, thetaOnIdeles_principal_mul]

@[simp] theorem adelicTheta_mk (f : Adeles F → ℂ) (g : Idele F) :
    adelicTheta F f (ideleClassMap F g) = thetaOnIdeles F f g := rfl

theorem adelicTheta_add {f h : Adeles F → ℂ} (hf : thetaSummable F f) (hh : thetaSummable F h) :
    adelicTheta F (f + h) = adelicTheta F f + adelicTheta F h := by
  funext c
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F c
  simp only [adelicTheta_mk, Pi.add_apply]
  exact (hf g).tsum_add (hh g)

theorem adelicTheta_continuous {f : Adeles F → ℂ} (h : Continuous (thetaOnIdeles F f)) :
    Continuous (adelicTheta F f) :=
  (QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff.mpr h

/-- Local uniform convergence is enough for the continuous conclusion of
Lemma 2.2.2.1 and Definition 2.2.3.1. The estimates giving it for all
Schwartz–Bruhat functions are separate. -/
theorem adelicTheta_continuous_of_locallyUniform {f : Adeles F → ℂ} (hf : Continuous f)
    (hsum : SummableLocallyUniformlyOn (fun ξ g => thetaSummand F f g ξ) univ) :
    Continuous (adelicTheta F f) := by
  apply adelicTheta_continuous
  obtain ⟨g, hg⟩ := hsum
  apply continuousOn_univ.mp
  apply ((hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).continuousOn ?_).congr
  · exact fun _ h => hg.tsum_eqOn h
  · exact Frequently.of_forall fun t => (continuous_finsetSum _ fun ξ _ =>
      hf.comp (Units.continuous_val.comp (continuous_const.mul continuous_id))).continuousOn

/-- The rational adelic product cut out by the printed archimedean
absolute-value bound and integrality at all finite places. -/
def printedRationalAdelicDomain : Set (NumberField.AdeleRing ℤ ℚ) :=
  {a | (∀ v : InfinitePlace ℚ, ‖a.1 v‖ < 1) ∧
    ∀ v : HeightOneSpectrum ℤ, a.2 v ∈ v.adicCompletionIntegers ℚ}

private theorem norm_rational_adelic_coordinate (v : InfinitePlace ℚ) (x : ℚ) :
    ‖(algebraMap ℚ (InfiniteAdeleRing ℚ) x) v‖ = (|x| : ℚ) := by
  change ‖(((WithAbs.equiv v.1).symm x : WithAbs v.1) : v.Completion)‖ = _
  rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply, Rat.cast_abs,
    ← Real.norm_eq_abs, Rat.norm_cast_real]
  simpa only [Rat.cast_id] using v.map_ratCast x

/-- The rational diagonal translate by 1 has nonempty intersection with the
printed domain, even with all finite-place conditions imposed. -/
theorem printed_rational_adelic_domain_overlap :
    ∃ a : NumberField.AdeleRing ℤ ℚ, a ∈ printedRationalAdelicDomain ∧
      a + algebraMap ℚ (NumberField.AdeleRing ℤ ℚ) 1 ∈ printedRationalAdelicDomain := by
  let a : NumberField.AdeleRing ℤ ℚ :=
    (algebraMap ℚ (InfiniteAdeleRing ℚ) (-1 / 2), 0)
  refine ⟨a, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro v
    change ‖(algebraMap ℚ (InfiniteAdeleRing ℚ) (-1 / 2)) v‖ < 1
    rw [norm_rational_adelic_coordinate]
    norm_num
  · intro v
    change (0 : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ
    exact zero_mem _
  · intro v
    change ‖((algebraMap ℚ (InfiniteAdeleRing ℚ) (-1 / 2)) v) +
      ((algebraMap ℚ (InfiniteAdeleRing ℚ) 1) v)‖ < 1
    have h : ((algebraMap ℚ (InfiniteAdeleRing ℚ) (-1 / 2)) v) +
        ((algebraMap ℚ (InfiniteAdeleRing ℚ) 1) v) =
        (algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2)) v := by
      have h' := congrArg (fun x : InfiniteAdeleRing ℚ => x v)
        (map_add (algebraMap ℚ (InfiniteAdeleRing ℚ)) (-1 / 2) 1)
      rw [show (-1 / 2 + 1 : ℚ) = 1 / 2 by norm_num] at h'
      exact h'.symm
    rw [h, norm_rational_adelic_coordinate]
    norm_num
  · intro v
    change ((0 : FiniteAdeleRing ℤ ℚ) +
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) 1) v ∈ v.adicCompletionIntegers ℚ
    simp only [zero_add, map_one]
    exact one_mem _

/-- The signed mixed-space lattice domain uses a coefficient for every
element of the integral basis, including both real directions at complex places. -/
def signedMixedDomain : Set (mixedEmbedding.mixedSpace F) :=
  ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem signedMixedDomain_isFundamental :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.integerLattice F) (signedMixedDomain F) :=
  mixedEmbedding.fundamentalDomain_integerLattice F

/-- The signed half-open interval is a genuine fundamental domain for integer
translation in the rational archimedean coordinate. -/
theorem signed_cube_unique_rep (x : ℝ) :
    ∃! n : ℤ, x - n ∈ Set.Ico (0 : ℝ) 1 := by
  refine ⟨⌊x⌋, ⟨sub_nonneg.mpr (Int.floor_le x), by linarith [Int.lt_floor_add_one x]⟩, ?_⟩
  intro n hn
  exact (Int.floor_eq_iff.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩).symm

end Masullo
