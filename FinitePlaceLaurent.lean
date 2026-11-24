import FinitePrincipalValue
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

open Function IsDedekindDomain NumberField Set Topology
open scoped BigOperators Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev Test := locallyConstantTests (K F v)

/-- The integer-unit invariant local tests, described by the norm orbits. -/
def finitePlaceRadial : Submodule ℂ (Test F v) where
  carrier := {f | ∀ x y, ‖x‖ = ‖y‖ → f.val x = f.val y}
  zero_mem' := by
    change ∀ x y : K F v, ‖x‖ = ‖y‖ → (0 : ℂ) = 0
    intros
    rfl
  add_mem' := by
    intro f g hf hg x y h
    change f.val x + g.val x = f.val y + g.val y
    rw [hf x y h, hg x y h]
  smul_mem' := by
    intro c f hf x y h
    change c * f.val x = c * f.val y
    rw [hf x y h]

theorem finitePlaceRadial_mem_iff (f : Test F v) :
    f ∈ finitePlaceRadial F v ↔
      ∀ u : (K F v)ˣ, ‖u.val‖ = 1 → ∀ x, f.val (u.val * x) = f.val x :=
  locallyConstantTests_radial_iff f

private theorem unitBall_compact : IsCompact (Metric.closedBall (0 : K F v) 1) := by
  rw [finiteCompletion_closedBall F v]
  exact finitePlaceIntegral_compact F v

private theorem unitBall_open : IsOpen (Metric.closedBall (0 : K F v) 1) := by
  rw [finiteCompletion_closedBall F v]
  exact Valued.isOpen_valuationSubring _

/-- The Laurent monomial of index `n` corresponds to the ball
`π ^ n * O_v`, viewed inside the integer-unit invariant tests. -/
def finitePlaceLaurentBall (π : (K F v)ˣ) (n : ℤ) : finitePlaceRadial F v :=
  ⟨radialBall π (unitBall_compact F v) (unitBall_open F v) n, by
    intro x y h
    rw [radialBall_apply, radialBall_apply, h]⟩

theorem finitePlaceLaurentBall_apply (π : (K F v)ˣ) (n : ℤ) (x : K F v) :
    (finitePlaceLaurentBall F v π n).val.val x = if ‖x‖ ≤ ‖π.val‖ ^ n then 1 else 0 :=
  radialBall_apply π (unitBall_compact F v) (unitBall_open F v) n x

/-- The norm ball is exactly the integer ring multiplied by the specified power. -/
theorem finitePlaceLaurentBall_indicator (π : (K F v)ˣ) (n : ℤ) (x : K F v) :
    (finitePlaceLaurentBall F v π n).val.val x =
      (((Homeomorph.smul (π ^ n) : K F v ≃ₜ K F v) : K F v → K F v) ''
        (v.adicCompletionIntegers F : Set (K F v))).indicator (fun _ => (1 : ℂ)) x := by
  rw [finitePlaceLaurentBall_apply, indicator_apply, ← finiteCompletion_closedBall F v]
  apply if_congr _ rfl rfl
  change _ ↔ x ∈ (Homeomorph.smul (π ^ n) : K F v ≃ₜ K F v).toEquiv '' Metric.closedBall 0 1
  rw [Set.mem_image_equiv, Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ ‖π.val‖ ^ n ↔ ‖(↑((π ^ n)⁻¹) : K F v) * x‖ ≤ 1
  rw [norm_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, norm_inv, norm_zpow,
    inv_mul_le_iff₀ (zpow_pos (norm_pos_iff.mpr π.ne_zero) _), mul_one]

theorem finitePlaceLaurentBall_zero (π : (K F v)ˣ) :
    (finitePlaceLaurentBall F v π 0).val = finiteCompletionIntegerRingTest F v := by
  apply Subtype.ext
  funext x
  rw [finitePlaceLaurentBall_apply, zpow_zero]
  change _ = (v.adicCompletionIntegers F : Set (K F v)).indicator (fun _ => (1 : ℂ)) x
  rw [← finiteCompletion_closedBall F v, indicator_apply, Metric.mem_closedBall, dist_zero_right]

private abbrev laurentBasis := AddMonoidAlgebra.basis ℤ ℂ

private def laurentBallMap (π : (K F v)ˣ) :
    LaurentPolynomial ℂ →ₗ[ℂ] finitePlaceRadial F v :=
  laurentBasis.constr ℂ (finitePlaceLaurentBall F v π)

private theorem laurentBallMap_monomial (π : (K F v)ˣ) (n : ℤ) :
    laurentBallMap F v π (LaurentPolynomial.T n) = finitePlaceLaurentBall F v π n :=
  laurentBasis.constr_basis ℂ _ n

private theorem laurentBallMap_injective (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    Injective (laurentBallMap F v π) := by
  let L := laurentBallMap F v π
  let D := (finitePrincipalValue π).comp ((finitePlaceRadial F v).subtype.comp L)
  have hm (m : ℤ) : (LinearMap.proj (π.val ^ m)).comp ((Test F v).subtype.comp D) =
      laurentBasis.coord m := by
    apply laurentBasis.ext
    intro n
    change (finitePrincipalValue π (L (LaurentPolynomial.T n)).val).val (π.val ^ m) = _
    rw [laurentBallMap_monomial]
    change (finitePrincipalValue π (radialBall π (unitBall_compact F v)
      (unitBall_open F v) n)).val (π.val ^ m) = _
    rw [finitePrincipalValue_radialBall π (finiteCompletion_uniformizer_contracts F v π hπ)
      (unitBall_compact F v) (unitBall_open F v) n m (norm_zpow _ _)]
    rw [laurentBasis.coord_apply, laurentBasis.repr_self, Finsupp.single_apply]
  intro P Q h
  apply laurentBasis.repr.injective
  ext m
  have he := DFunLike.congr_fun (hm m) P
  have he' := DFunLike.congr_fun (hm m) Q
  change (finitePrincipalValue π (L P).val).val (π.val ^ m) = laurentBasis.repr P m at he
  change (finitePrincipalValue π (L Q).val).val (π.val ^ m) = laurentBasis.repr Q m at he'
  rw [← he, ← he', h]

private theorem laurentBallMap_surjective (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    Surjective (laurentBallMap F v π) := by
  intro f
  have hc := finiteCompletion_uniformizer_contracts F v π hπ
  obtain ⟨I, c, he⟩ := finitePrincipalValue_radial_range_sum π hc
    (unitBall_compact F v) (unitBall_open F v) (finiteCompletion_norm_zpow F v π hπ)
    (finitePrincipalValue π f.val) (finitePrincipalValue_radial π f.val f.property)
    (finitePrincipalValue_eval_zero π f.val)
  refine ⟨∑ n ∈ I, c n • LaurentPolynomial.T n, ?_⟩
  apply Subtype.ext
  apply finitePrincipalValue_injective π hc
  simp only [map_sum, map_smul, laurentBallMap_monomial]
  change finitePrincipalValue π ((finitePlaceRadial F v).subtype
    (∑ n ∈ I, c n • finitePlaceLaurentBall F v π n)) = _
  simp only [map_sum, map_smul]
  change (∑ n ∈ I, c n • finitePrincipalValue π
    (radialBall π (unitBall_compact F v) (unitBall_open F v) n)) = _
  simpa only [map_sum, map_smul] using he

def translateRadial (u : (K F v)ˣ) : finitePlaceRadial F v →ₗ[ℂ] finitePlaceRadial F v :=
  (locallyConstantTestTranslate _ u).restrict fun f hf x y h => by
    change (locallyConstantTestTranslate _ u f).val x = (locallyConstantTestTranslate _ u f).val y
    apply hf
    change ‖(↑u⁻¹ : K F v) * x‖ = ‖(↑u⁻¹ : K F v) * y‖
    rw [norm_mul, norm_mul, h]

/-- Uniformizer translation raises the radius exponent of the radial ball by one. -/
theorem translateRadial_ball (π : (K F v)ˣ) (n : ℤ) :
    translateRadial F v π (finitePlaceLaurentBall F v π n) =
      finitePlaceLaurentBall F v π (n + 1) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (finitePlaceLaurentBall F v π n).val.val ((↑π⁻¹ : K F v) * x) = _
  rw [finitePlaceLaurentBall_apply, finitePlaceLaurentBall_apply, Units.val_inv_eq_inv_val,
    norm_mul, norm_inv]
  apply if_congr _ rfl rfl
  rw [inv_mul_le_iff₀ (norm_pos_iff.mpr π.ne_zero),
    mul_comm ‖π.val‖, ← zpow_add_one₀ (norm_ne_zero_iff.mpr π.ne_zero)]

theorem laurentBallMap_translate (π : (K F v)ˣ) (P : LaurentPolynomial ℂ) :
    laurentBallMap F v π (LaurentPolynomial.T 1 * P) =
      translateRadial F v π (laurentBallMap F v π P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, map_add, hp, hq]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.smul_eq_C_mul, mul_smul_comm, map_smul, map_smul, map_smul,
      ← LaurentPolynomial.T_add, laurentBallMap_monomial, laurentBallMap_monomial,
      translateRadial_ball, Int.add_comm 1 n]

local instance : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
local instance : TopologicalSpace (LaurentPolynomial ℂ) := finestLocallyConvexTopology _

/-- Lemma 6.1.2.2(1). The Laurent map is a linear homeomorphism, with
`T` acting by inverse-argument uniformizer translation. -/
def finitePlaceLaurentEquiv (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    LaurentPolynomial ℂ ≃L[ℂ] finitePlaceRadial F v := by
  let e := LinearEquiv.ofBijective (laurentBallMap F v π)
    ⟨laurentBallMap_injective F v π hπ, laurentBallMap_surjective F v π hπ⟩
  letI : PolynormableSpace ℂ (LaurentPolynomial ℂ) := (finest_withSeminorms _).toPolynormableSpace
  letI : PolynormableSpace ℂ (Test F v) := (finest_withSeminorms _).toPolynormableSpace
  have htop := (finest_submodule_quotient (finitePlaceRadial F v)).2.2.1
  refine ⟨e, ?_, ?_⟩
  · exact (finest_linear_continuous
      (F := Test F v) ((finitePlaceRadial F v).subtype.comp (laurentBallMap F v π))).subtype_mk _
  · change Continuous e.symm.toLinearMap
    exact Eq.mpr (congrArg (fun t : TopologicalSpace (finitePlaceRadial F v) =>
      Continuous[t, inferInstance] e.symm.toLinearMap) htop)
      (finest_linear_continuous (E := ↥(finitePlaceRadial F v))
        (F := LaurentPolynomial ℂ) e.symm.toLinearMap)

theorem finitePlaceLaurentEquiv_monomial (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (n : ℤ) :
    finitePlaceLaurentEquiv F v π hπ (LaurentPolynomial.T n) = finitePlaceLaurentBall F v π n :=
  laurentBallMap_monomial F v π n

theorem finitePlaceLaurentEquiv_translate (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (P : LaurentPolynomial ℂ) :
    finitePlaceLaurentEquiv F v π hπ (LaurentPolynomial.T 1 * P) =
      translateRadial F v π (finitePlaceLaurentEquiv F v π hπ P) :=
  laurentBallMap_translate F v π P

theorem finitePlaceRadial_closed : IsClosed (finitePlaceRadial F v : Set (Test F v)) :=
  (finest_submodule_quotient (finitePlaceRadial F v)).2.1

/-- The Laurent module structure on the existing complex vector space. -/
abbrev finitePlaceLaurentModule (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    Module (LaurentPolynomial ℂ) (finitePlaceRadial F v) :=
  (finitePlaceLaurentEquiv F v π hπ).symm.toLinearEquiv.toAddEquiv.module _

theorem finitePlaceLaurentModule_smul_T (π : (K F v)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (f : finitePlaceRadial F v) :
    letI := finitePlaceLaurentModule F v π hπ
    LaurentPolynomial.T (R := ℂ) 1 • f = translateRadial F v π f := by
  letI := finitePlaceLaurentModule F v π hπ
  let e := finitePlaceLaurentEquiv F v π hπ
  change e (LaurentPolynomial.T 1 * e.symm f) = _
  rw [finitePlaceLaurentEquiv_translate, ContinuousLinearEquiv.apply_symm_apply]

theorem finitePlaceLaurentModule_smul_C (π : (K F v)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (a : ℂ) (f : finitePlaceRadial F v) :
    letI := finitePlaceLaurentModule F v π hπ
    LaurentPolynomial.C a • f = a • f := by
  letI := finitePlaceLaurentModule F v π hπ
  let e := finitePlaceLaurentEquiv F v π hπ
  change e (LaurentPolynomial.C a * e.symm f) = _
  rw [← LaurentPolynomial.smul_eq_C_mul, map_smul, ContinuousLinearEquiv.apply_symm_apply]

/-- The rank-one basis over the Laurent polynomials consists of the
integer-ring indicator. -/
def finitePlaceLaurentModule_basis (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    letI := finitePlaceLaurentModule F v π hπ
    Module.Basis Unit (LaurentPolynomial ℂ) (finitePlaceRadial F v) := by
  letI := finitePlaceLaurentModule F v π hπ
  let e := (finitePlaceLaurentEquiv F v π hπ).symm.toLinearEquiv.toAddEquiv
  exact (Module.Basis.singleton Unit (LaurentPolynomial ℂ)).map
    (e.linearEquiv (A := LaurentPolynomial ℂ)).symm

theorem finitePlaceLaurentModule_basis_apply (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    letI := finitePlaceLaurentModule F v π hπ
    ((finitePlaceLaurentModule_basis F v π hπ) ()).val = finiteCompletionIntegerRingTest F v := by
  letI := finitePlaceLaurentModule F v π hπ
  simp only [finitePlaceLaurentModule_basis, Module.Basis.map_apply, Module.Basis.singleton_apply]
  change ((finitePlaceLaurentEquiv F v π hπ) 1).val = _
  rw [← LaurentPolynomial.T_zero, finitePlaceLaurentEquiv_monomial, finitePlaceLaurentBall_zero]

def uniformizerRepresentative (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (x : K F v) : K F v :=
  if hx : x = 0 then 0 else π.val ^ (finiteCompletion_norm_zpow F v π hπ x hx).choose

theorem norm_uniformizerRepresentative (π : (K F v)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (x : K F v) :
    ‖uniformizerRepresentative F v π hπ x‖ = ‖x‖ := by
  unfold uniformizerRepresentative
  split
  · next hx => rw [hx]
  · next hx =>
    rw [norm_zpow]
    exact (finiteCompletion_norm_zpow F v π hπ x hx).choose_spec.symm

theorem uniformizerRepresentative_eq_of_norm_eq (π : (K F v)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) {x y : K F v} (h : ‖x‖ = ‖y‖) :
    uniformizerRepresentative F v π hπ x = uniformizerRepresentative F v π hπ y := by
  have hc := finiteCompletion_uniformizer_contracts F v π hπ
  have hr := norm_pos_iff.mpr π.ne_zero
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by simpa [hx] using h.symm)
    rw [hx, hy]
  · have hy : y ≠ 0 := fun hy => hx (norm_eq_zero.mp (by simpa [hy] using h))
    unfold uniformizerRepresentative
    rw [dite_eq_right hx, dite_eq_right hy]
    congr 1
    apply zpow_right_injective₀ hr hc.ne
    exact (finiteCompletion_norm_zpow F v π hπ x hx).choose_spec.symm.trans
      (h.trans (finiteCompletion_norm_zpow F v π hπ y hy).choose_spec)

private theorem norm_eventually_eq_of_ne_zero (π : (K F v)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) {x : K F v} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, ‖y‖ = ‖x‖ := by
  obtain ⟨m, hm⟩ := finiteCompletion_norm_zpow F v π hπ x hx
  have hc := finiteCompletion_uniformizer_contracts F v π hπ
  have hr := norm_pos_iff.mpr π.ne_zero
  let r := ‖π.val‖
  have hleft : r ^ (m + 1) < ‖x‖ := by
    rw [hm]
    exact (zpow_lt_zpow_iff_right_of_lt_one₀ hr hc).mpr (by omega)
  have hright : ‖x‖ < r ^ (m - 1) := by
    rw [hm]
    exact (zpow_lt_zpow_iff_right_of_lt_one₀ hr hc).mpr (by omega)
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hleft,
    (isOpen_lt continuous_norm continuous_const).mem_nhds hright] with y h₁ h₂
  have hy : y ≠ 0 := norm_pos_iff.mp ((zpow_pos hr _).trans h₁)
  obtain ⟨n, hn⟩ := finiteCompletion_norm_zpow F v π hπ y hy
  change r ^ (m + 1) < ‖y‖ at h₁
  change ‖y‖ < r ^ (m - 1) at h₂
  rw [hn] at h₁ h₂
  have h₁' := (zpow_lt_zpow_iff_right_of_lt_one₀ hr hc).mp h₁
  have h₂' := (zpow_lt_zpow_iff_right_of_lt_one₀ hr hc).mp h₂
  rw [hm, hn, show n = m by omega]

/-- Replacing a point by its uniformizer power of equal norm preserves the
local test conditions and projects the test space onto its unit invariants. -/
def finitePlaceRadialProjection (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    Test F v →ₗ[ℂ] finitePlaceRadial F v := by
  let p := uniformizerRepresentative F v π hπ
  have hp (x : K F v) : ‖p x‖ = ‖x‖ := norm_uniformizerRepresentative F v π hπ x
  have hEq (x y : K F v) (h : ‖x‖ = ‖y‖) : p x = p y :=
    uniformizerRepresentative_eq_of_norm_eq F v π hπ h
  have h0 : p 0 = 0 := dite_eq_left rfl
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  have hc := finiteCompletion_uniformizer_contracts F v π hπ
  letI : NontriviallyNormedField (K F v) :=
    ⟨⟨π.val⁻¹, by rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr π.ne_zero)).mpr hc⟩⟩
  letI : ProperSpace (K F v) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let R (f : Test F v) : Test F v := by
    refine ⟨f.val ∘ p, ?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x = 0
      · subst x
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (f.property.1.eventually_eq 0)
        filter_upwards [Metric.ball_mem_nhds (0 : K F v) hε] with y hy
        have hpy : p y ∈ Metric.ball 0 ε := by
          simpa only [Metric.mem_ball, dist_zero_right, hp] using hy
        change f.val (p y) = f.val (p 0)
        rw [h0]
        exact hball hpy
      · filter_upwards [norm_eventually_eq_of_ne_zero F v π hπ hx] with y hy
        exact congrArg f.val (hEq y x hy)
    · obtain ⟨R, hR⟩ := f.property.2.isBounded.subset_closedBall (0 : K F v)
      apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : K F v) R)
      intro y hy
      have hy' : p y ∈ tsupport f.val := subset_tsupport _ hy
      simpa only [Metric.mem_closedBall, dist_zero_right, hp] using hR hy'
  exact
    { toFun := fun f => ⟨R f, fun x y h => congrArg f.val (hEq x y h)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem finitePlaceRadialProjection_apply (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (f : Test F v) (x : K F v) :
    (finitePlaceRadialProjection F v π hπ f).val.val x =
      f.val (uniformizerRepresentative F v π hπ x) := rfl

theorem finitePlaceRadialProjection_fixes (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (f : finitePlaceRadial F v) : finitePlaceRadialProjection F v π hπ f.val = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact f.property _ _ (norm_uniformizerRepresentative F v π hπ x)

end
end Masullo
