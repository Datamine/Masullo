/-
The uniform Cauchy estimate follows the argument in the Apache-2.0
RiemannMasullo project, commit 5a2eadc. See External/PROVENANCE.md.
-/
import BergmanDivisibility
import MellinBergman
import MappingSpaces
import TopologicalLinearLimits

open Bornology Filter Function Set Topology
open scoped ENat

namespace Masullo

noncomputable section

private abbrev Bergman := SchwartzBergman (univ : Set ℝ)

/-- The (m)-th Taylor coefficient is a continuous functional on the entire
Schwartz–Bergman space. -/
def bergmanNormalizedJet (z : ℂ) (m : ℕ) : StrongDual ℂ Bergman :=
  (m.factorial : ℂ)⁻¹ • Classical.choose
    (exists_schwartzBergman_jetEvaluation (I := univ) isOpen_univ ordConnected_univ z
      (mem_univ z.re) m)

theorem bergmanNormalizedJet_apply (z : ℂ) (m : ℕ) (f : Bergman) :
    bergmanNormalizedJet z m f = (m.factorial : ℂ)⁻¹ * iteratedDeriv m f.val z := by
  unfold bergmanNormalizedJet
  rw [smul_apply, smul_eq_mul, Classical.choose_spec
    (exists_schwartzBergman_jetEvaluation (I := univ) isOpen_univ ordConnected_univ z
      (mem_univ z.re) m)]

private theorem entire_of_bergman (f : Bergman) : Differentiable ℂ f.val := by
  have h := f.property.2.1
  simpa only [preimage_univ, differentiableOn_univ] using h

/-- All normalized jets, of every order and height, are bounded on each
test by its supremum on a common enlarged strip. -/
theorem bergmanNormalizedJet_pointwise_bound (a b : ℝ) (hab : a ≤ b) (f : Bergman) :
    ∃ M : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ∀ m : ℕ, ‖bergmanNormalizedJet z m f‖ ≤ M := by
  obtain ⟨M, hM⟩ := f.property.2.2 (a - 1) (b + 1) (by linarith) (subset_univ _) 0
  refine ⟨M, fun z hz m ↦ ?_⟩
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z 1) : ‖f.val w‖ ≤ M := by
    have hd := (Complex.abs_re_le_norm (w - z)).trans
      (mem_closedBall_iff_norm.mp (Metric.sphere_subset_closedBall hw))
    rw [Complex.sub_re, abs_le] at hd
    have hs : w.re ∈ Icc (a - 1) (b + 1) := ⟨by linarith [hd.1, hz.1],
      by linarith [hd.2, hz.2]⟩
    have h := hM (show ‖w ^ 0 * f.val w‖ ∈ _ from ⟨w, hs, rfl⟩)
    simpa using h
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m one_pos
    (entire_of_bergman f).diffContOnCl hcircle
  rw [bergmanNormalizedJet_apply, norm_mul, norm_inv, Complex.norm_natCast,
    inv_mul_le_iff₀ (by positivity)]
  simpa only [one_pow, div_one, mul_comm] using h

private theorem range_bounded_of_equicontinuous
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (J : ι → StrongDual ℂ E) (h : Equicontinuous (fun i (f : E) ↦ J i f)) :
    IsVonNBounded ℂ (range J) := by
  have h' : Equicontinuous (fun j : range J ↦ (j.val : E → ℂ)) := by
    choose g hg using fun j : range J ↦ j.property
    simpa only [Function.comp_def, hg] using h.comp g
  exact equicontinuous_mappingSpace_bounded (range J) h'
    {B : Set E | IsVonNBounded ℂ B} fun _ hB ↦ hB

/-- The normalized jets on a closed strip are equicontinuous and bounded
in the strong dual. -/
theorem bergmanNormalizedJet_family (a b : ℝ) (hab : a ≤ b) :
    let J (i : {z : ℂ // z.re ∈ Icc a b} × ℕ) := bergmanNormalizedJet i.1 i.2
    Equicontinuous (fun i (f : Bergman) ↦ J i f) ∧ IsVonNBounded ℂ (range J) := by
  intro J
  letI : BarrelledSpace ℂ Bergman :=
    isFrechetTVS_barrelled (schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty)
  letI : ContinuousSMul ℂ Bergman := (PolynormableSpace.withSeminorms ℂ Bergman).continuousSMul
  have hpt (f : Bergman) : IsVonNBounded ℂ (range fun i ↦ J i f) := by
    obtain ⟨M, hM⟩ := bergmanNormalizedJet_pointwise_bound a b hab f
    refine (NormedSpace.isVonNBounded_iff' ℂ).mpr ⟨M, ?_⟩
    rintro _ ⟨⟨z, m⟩, rfl⟩
    exact hM z z.property m
  have he := (PolynormableSpace.banach_steinhaus (𝓕 := J) hpt).equicontinuous
  exact ⟨he, range_bounded_of_equicontinuous J he⟩

/-- Taylor jets with a prescribed set of centers and orders descend to any
quotient whose denominator they annihilate. Their strong bounds persist in the quotient. -/
theorem bergmanNormalizedJet_quotient (a b : ℝ) (hab : a ≤ b) (W : Submodule ℂ Bergman)
    (S : Set ({z : ℂ // z.re ∈ Icc a b} × ℕ))
    (hW : ∀ i : S, W ≤ (bergmanNormalizedJet i.val.1 i.val.2).ker) :
    ∃ J : S → StrongDual ℂ (Bergman ⧸ W),
      (∀ i f, J i (W.mkQ f) = bergmanNormalizedJet i.val.1 i.val.2 f) ∧
      Equicontinuous (fun i (f : Bergman ⧸ W) ↦ J i f) ∧ IsVonNBounded ℂ (range J) := by
  letI : IsTopologicalAddGroup Bergman :=
    (PolynormableSpace.withSeminorms ℂ Bergman).topologicalAddGroup
  let J (i : S) := W.liftQL (bergmanNormalizedJet i.val.1 i.val.2) (hW i)
  have hE : Equicontinuous (fun i : S ↦ (bergmanNormalizedJet i.val.1 i.val.2 : Bergman → ℂ)) :=
    (bergmanNormalizedJet_family a b hab).1.comp Subtype.val
  have hv (i : S) (f : Bergman) : J i (W.mkQ f) = bergmanNormalizedJet i.val.1 i.val.2 f := rfl
  have hq : Equicontinuous (fun i (f : Bergman ⧸ W) ↦ J i f) := by
    intro g
    obtain ⟨f, rfl⟩ := W.mkQ_surjective g
    apply Metric.equicontinuousAt_iff_right.mpr
    intro e he
    have hU := Metric.equicontinuousAt_iff_right.mp (hE f) e he
    have hmap := W.isOpenMap_mkQ.map_nhds_eq (W.mkQL.continuous.continuousAt : ContinuousAt W.mkQL f)
    rw [← hmap]
    filter_upwards [Filter.image_mem_map hU] with x hx
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    rw [hv, hv]
    exact hy i
  exact ⟨J, hv, hq, range_bounded_of_equicontinuous J hq⟩

/-- The closed divisibility denominator is the common kernel of the jets
strictly below the divisor orders. -/
def bergmanDivisorSubmodule (g : ℂ → ℂ) : Submodule ℂ Bergman :=
  ⨅ i : {i : ℂ × ℕ // (i.2 : ℕ∞) < analyticOrderAt g i.1},
    (bergmanNormalizedJet i.val.1 i.val.2).ker

theorem bergmanDivisorSubmodule_mem_iff {g : ℂ → ℂ} (hg : Differentiable ℂ g) (f : Bergman) :
    f ∈ bergmanDivisorSubmodule g ↔ ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, f.val z = g z * k z := by
  rw [entire_divisibility_iff_orders hg (entire_of_bergman f)]
  simp only [bergmanDivisorSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, bergmanNormalizedJet_apply, mul_eq_zero,
    inv_eq_zero, Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or]
  constructor
  · intro h z
    rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((entire_of_bergman f).analyticAt z)]
    intro m hm
    exact h ⟨(z, m), (by exact_mod_cast hm : (m : ℕ∞) < n).trans_le hn⟩
  · intro h i
    let z := i.val.1
    let m := i.val.2
    have hm : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g z := by
      simpa only [Nat.cast_add, Nat.cast_one] using ((ENat.add_one_le_iff (ENat.natCast_ne_top m)).mpr i.property)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((entire_of_bergman f).analyticAt z)).mp (hm.trans (h z)) m (Nat.lt_succ_self m)

theorem bergmanDivisorSubmodule_isClosed {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    IsClosed (bergmanDivisorSubmodule g : Set Bergman) := by
  convert schwartzBergman_entireDivisibility_isClosed hg using 1
  ext f
  exact bergmanDivisorSubmodule_mem_iff hg f


/-- The closed denominator that forgets Taylor coordinates of order at
least `N`, retaining all lower coordinates present in the original divisor. -/
def bergmanTruncatedDivisorSubmodule (g : ℂ → ℂ) (N : ℕ) : Submodule ℂ Bergman :=
  ⨅ i : {i : ℂ × ℕ // i.2 < N ∧ (i.2 : ℕ∞) < analyticOrderAt g i.1},
    (bergmanNormalizedJet i.val.1 i.val.2).ker

theorem bergmanTruncatedDivisorSubmodule_mem_iff (g : ℂ → ℂ) (N : ℕ) (f : Bergman) :
    f ∈ bergmanTruncatedDivisorSubmodule g N ↔
      ∀ z, min (N : ℕ∞) (analyticOrderAt g z) ≤ analyticOrderAt f.val z := by
  simp only [bergmanTruncatedDivisorSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, bergmanNormalizedJet_apply, mul_eq_zero, inv_eq_zero,
    Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or]
  constructor
  · intro h z
    rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((entire_of_bergman f).analyticAt z)).mpr
    intro m hm
    have hmn : (m : ℕ∞) < n := by exact_mod_cast hm
    exact h ⟨(z, m), by exact_mod_cast hmn.trans_le (hn.trans (min_le_left _ _)),
      hmn.trans_le (hn.trans (min_le_right _ _))⟩
  · intro h i
    have hi : (i.val.2 : ℕ∞) < min (N : ℕ∞) (analyticOrderAt g i.val.1) :=
      lt_min (by exact_mod_cast i.property.1) i.property.2
    have hm : ((i.val.2 + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f.val i.val.1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((ENat.add_one_le_iff (ENat.natCast_ne_top i.val.2)).mpr
          (hi.trans_le (h i.val.1)))
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((entire_of_bergman f).analyticAt i.val.1)).mp hm i.val.2 (Nat.lt_succ_self _)

theorem bergmanTruncatedDivisorSubmodule_isClosed (g : ℂ → ℂ) (N : ℕ) :
    IsClosed (bergmanTruncatedDivisorSubmodule g N : Set Bergman) := by
  simp only [bergmanTruncatedDivisorSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun _ ↦ isClosed_singleton.preimage (bergmanNormalizedJet _ _).continuous

theorem bergmanDivisorSubmodule_le_truncated (g : ℂ → ℂ) (N : ℕ) :
    bergmanDivisorSubmodule g ≤ bergmanTruncatedDivisorSubmodule g N := by
  apply le_iInf
  intro i
  let j : {j : ℂ × ℕ // (j.2 : ℕ∞) < analyticOrderAt g j.1} := ⟨i.val, i.property.2⟩
  exact iInf_le (fun j : {j : ℂ × ℕ // (j.2 : ℕ∞) < analyticOrderAt g j.1} ↦
    (bergmanNormalizedJet j.val.1 j.val.2).ker) j

/-- Every entire multiplier that acts on the test space induces a continuous
operator on the truncated quotient. -/
theorem bergmanTruncatedDivisor_lift (g : ℂ → ℂ) (N : ℕ)
    (A : Bergman →L[ℂ] Bergman) (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hA : ∀ f z, (A f).val z = p z * f.val z) :
    let W := bergmanTruncatedDivisorSubmodule g N
    ∃ T : (Bergman ⧸ W) →L[ℂ] (Bergman ⧸ W), ∀ f, T (W.mkQ f) = W.mkQ (A f) := by
  intro W
  letI : IsTopologicalAddGroup Bergman :=
    (PolynormableSpace.withSeminorms ℂ Bergman).topologicalAddGroup
  have hW : W ≤ (W.mkQL.comp A).ker := by
    intro f hf
    change A f ∈ W.mkQ.ker
    rw [W.ker_mkQ]
    rw [bergmanTruncatedDivisorSubmodule_mem_iff] at hf ⊢
    intro z
    have he : (A f).val = fun w ↦ p w * f.val w := funext (hA f)
    rw [he]
    change _ ≤ analyticOrderAt (p * f.val) z
    rw [analyticOrderAt_mul (hp.analyticAt z) ((entire_of_bergman f).analyticAt z)]
    exact (hf z).trans (le_add_of_nonneg_left zero_le)
  exact ⟨W.liftQL (W.mkQL.comp A) hW, fun _ ↦ rfl⟩

#print axioms bergmanTruncatedDivisor_lift

/-- The normalized spectral jets on the divisibility quotient are
equicontinuous and strongly bounded, for all orders below the divisor. -/
theorem bergmanDivisor_normalizedJets (g : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b) :
    let S : Set ({z : ℂ // z.re ∈ Icc a b} × ℕ) :=
      {i | (i.2 : ℕ∞) < analyticOrderAt g i.1}
    ∃ J : S → StrongDual ℂ (Bergman ⧸ bergmanDivisorSubmodule g),
      (∀ i f, J i ((bergmanDivisorSubmodule g).mkQ f) =
        (i.val.2.factorial : ℂ)⁻¹ * iteratedDeriv i.val.2 f.val i.val.1) ∧
      Equicontinuous (fun i (f : Bergman ⧸ bergmanDivisorSubmodule g) ↦ J i f) ∧
      IsVonNBounded ℂ (range J) := by
  intro S
  have hW (i : S) :
      bergmanDivisorSubmodule g ≤ (bergmanNormalizedJet i.val.1 i.val.2).ker := by
    let j : {i : ℂ × ℕ // (i.2 : ℕ∞) < analyticOrderAt g i.1} :=
      ⟨(i.val.1.val, i.val.2), i.property⟩
    exact iInf_le (fun j : {i : ℂ × ℕ // (i.2 : ℕ∞) < analyticOrderAt g i.1} ↦
      (bergmanNormalizedJet j.val.1 j.val.2).ker) j
  obtain ⟨J, hv, he, hb⟩ := bergmanNormalizedJet_quotient a b hab (bergmanDivisorSubmodule g) S hW
  exact ⟨J, fun i f ↦ (hv i f).trans (bergmanNormalizedJet_apply _ _ _), he, hb⟩

/-- If the strip contains the entire divisor, the descended jets separate the
quotient. This gives the exact kernel of the jet coordinates. -/
theorem bergmanDivisor_normalizedJets_separate (g : ℂ → ℂ) (a b : ℝ)
    (hstrip : ∀ z : ℂ, 0 < analyticOrderAt g z → z.re ∈ Icc a b) :
    let S : Set ({z : ℂ // z.re ∈ Icc a b} × ℕ) :=
      {i | (i.2 : ℕ∞) < analyticOrderAt g i.1}
    ∀ J : S → StrongDual ℂ (Bergman ⧸ bergmanDivisorSubmodule g),
      (∀ i f, J i ((bergmanDivisorSubmodule g).mkQ f) =
        bergmanNormalizedJet i.val.1 i.val.2 f) →
      ∀ u : Bergman ⧸ bergmanDivisorSubmodule g, (∀ i, J i u = 0) ↔ u = 0 := by
  intro S J hJ u
  let W := bergmanDivisorSubmodule g
  constructor
  · intro hu
    obtain ⟨f, rfl⟩ := W.mkQ_surjective u
    apply (Submodule.Quotient.mk_eq_zero W).mpr
    change f ∈ bergmanDivisorSubmodule g
    simp only [bergmanDivisorSubmodule, Submodule.mem_iInf]
    intro j
    have hz : j.val.1.re ∈ Icc a b := hstrip j.val.1 ((bot_le : (0 : ℕ∞) ≤ (j.val.2 : ℕ∞)).trans_lt j.property)
    let i : S := ⟨(⟨j.val.1, hz⟩, j.val.2), j.property⟩
    change bergmanNormalizedJet j.val.1 j.val.2 f = 0
    exact (hJ i f).symm.trans (hu i)
  · rintro rfl i
    exact map_zero (J i)

end

end Masullo
