/-
The comparison of ideal-norm coefficients with the finite Euler product is
used in the RiemannMasullo proof of B.6.1.2(2) at 4cb67a2. This file proves the
comparison for the local ideal weight and Euler product.
-/
import HeckeIdealAsymptotics
import ManuscriptHeckeCharacterChart
import DedekindEulerProduct

open Filter Function Ideal IsDedekindDomain NumberField Set Topology UniqueFactorizationMonoid
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

omit [NumberField F] in
private theorem primeIdeal_injective : Injective (HeightOneSpectrum.asIdeal : Place F → _) :=
  fun _ _ h ↦ HeightOneSpectrum.ext h

private theorem finite_weight_factors (χ : PontryaginDual (IdeleClass F)) (I : Ideal (𝓞 F)) :
    HasFiniteMulSupport (fun v : Place F ↦
      heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v ^
        Multiset.count v.asIdeal (normalizedFactors I)) := by
  classical
  apply (((normalizedFactors I).toFinset.finite_toSet).preimage
    (primeIdeal_injective F).injOn).subset
  intro v hv
  by_contra hn
  have hz : Multiset.count v.asIdeal (normalizedFactors I) = 0 :=
    Multiset.count_eq_zero_of_notMem (by simpa only [Set.mem_preimage, Finset.mem_coe,
      Multiset.mem_toFinset] using hn)
  apply hv
  change _ ^ Multiset.count v.asIdeal (normalizedFactors I) = 1
  rw [hz, pow_zero]

private theorem finiteHeckeIdealWeight_mul (χ : PontryaginDual (IdeleClass F))
    (I J : Ideal (𝓞 F)) :
    finiteHeckeIdealWeight F χ (I * J) =
      finiteHeckeIdealWeight F χ I * finiteHeckeIdealWeight F χ J := by
  classical
  by_cases hI : I = 0
  · simp [hI, finiteHeckeIdealWeight]
  by_cases hJ : J = 0
  · simp [hJ, finiteHeckeIdealWeight]
  have hIJ := mul_ne_zero hI hJ
  have hI' : I ≠ ⊥ := hI
  have hJ' : J ≠ ⊥ := hJ
  have hIJ' : I * J ≠ ⊥ := hIJ
  simp only [finiteHeckeIdealWeight, hIJ', hI', hJ', ite_false, normalizedFactors_mul hI hJ,
    Multiset.count_add, pow_add]
  exact finprod_mul_distrib (finite_weight_factors F χ I) (finite_weight_factors F χ J)

private theorem finiteHeckeIdealWeight_top (χ : PontryaginDual (IdeleClass F)) :
    finiteHeckeIdealWeight F χ (1 : Ideal (𝓞 F)) = 1 := by
  have h : (1 : Ideal (𝓞 F)) ≠ ⊥ := one_ne_zero
  rw [finiteHeckeIdealWeight, ite_eq_right h]
  apply finprod_eq_one_of_forall_eq_one
  intro v
  rw [normalizedFactors_one, Multiset.count_zero, pow_zero]

theorem norm_finiteHeckeIdealWeight_le_one (χ : PontryaginDual (IdeleClass F))
    (I : Ideal (𝓞 F)) : ‖finiteHeckeIdealWeight F χ I‖ ≤ 1 := by
  classical
  by_cases hI : I = ⊥
  · simp [finiteHeckeIdealWeight, hI]
  let S := (finite_weight_factors F χ I).toFinset
  have hS : mulSupport (fun v : Place F ↦
      heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v ^
        Multiset.count v.asIdeal (normalizedFactors I)) ⊆ ↑S := by
    intro v hv
    exact (finite_weight_factors F χ I).mem_toFinset.mpr hv
  rw [finiteHeckeIdealWeight, ite_eq_right hI, finprod_eq_prod_of_mulSupport_subset _ hS, norm_prod]
  exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
    (fun v _ ↦ by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_heckeEulerCoefficient_le_one F χ _ v))

private theorem finiteHeckeIdealWeight_prime (χ : PontryaginDual (IdeleClass F)) (v : Place F) :
    finiteHeckeIdealWeight F χ v.asIdeal =
      heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v := by
  classical
  rw [finiteHeckeIdealWeight, ite_eq_right v.ne_bot, normalizedFactors_irreducible v.prime.irreducible]
  rw [normalize_eq, finprod_eq_single _ v]
  · simp
  · intro w hw
    have hn := fun h ↦ hw ((primeIdeal_injective F) h)
    change _ ^ Multiset.count w.asIdeal ({v.asIdeal} : Multiset _) = 1
    rw [Multiset.count_singleton, ite_eq_right hn, pow_zero]

/-- The coefficient at a positive ideal norm is the sum of the actual weights on its fibre. -/
def finiteHeckeNormCoefficient (χ : PontryaginDual (IdeleClass F)) (n : ℕ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I.absNorm = n}, finiteHeckeIdealWeight F χ I.val

private theorem norm_absNorm_cpow (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  obtain rfl | hn := eq_or_ne n 0
  · have hz : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [Complex.zero_cpow (neg_ne_zero.mpr hz), Real.zero_rpow (by linarith : -s.re ≠ 0)]
  exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn) _

set_option maxHeartbeats 1300000 in
/-- The finite Euler product on the open right half-plane is the norm Dirichlet
series for the local ideal weights, including zero coefficients at ramified primes. -/
theorem manuscriptFiniteHeckeEuler_hasSum_normCoefficients
    (χ : PontryaginDual (IdeleClass F)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (finiteHeckeNormCoefficient F χ) s
      (manuscriptFiniteHeckeEuler F χ s) := by
  classical
  let f : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun I := finiteHeckeIdealWeight F χ I * (I.absNorm : ℂ) ^ (-s)
      map_zero' := by simp [finiteHeckeIdealWeight]
      map_one' := by rw [finiteHeckeIdealWeight_top, one_mul, map_one, Nat.cast_one, Complex.one_cpow]
      map_mul' I J := by
        simp only [finiteHeckeIdealWeight_mul, map_mul, Nat.cast_mul]
        have hcp := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) I.absNorm)
          (Nat.cast_nonneg (α := ℝ) J.absNorm) (-s)
        push_cast at hcp
        rw [hcp]
        ring }
  have hf (I : Ideal (𝓞 F)) : ‖f I‖ ≤ (I.absNorm : ℝ) ^ (-s.re) := by
    change ‖finiteHeckeIdealWeight F χ I * (I.absNorm : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, norm_absNorm_cpow s hs]
    exact mul_le_of_le_one_left (by positivity) (norm_finiteHeckeIdealWeight_le_one F χ I)
  have hsum : Summable fun I ↦ ‖f I‖ :=
    (summable_absNorm_rpow F hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hf
  have hprime (v : Place F) : ‖f v.asIdeal‖ < 1 :=
    (hf _).trans_lt (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith : -s.re < 0))
  have hp := hasProd_eulerFactors_of_summable (fun v : Place F ↦ v.asIdeal)
    (fun v ↦ v.prime) (fun v w hvw ↦ HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hvw)).symm)
    (fun I hI htop ↦ by
      obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using htop)
      exact ⟨⟨J, hJ.isPrime, fun he ↦ hI (le_bot_iff.mp (he ▸ hIJ))⟩, Ideal.dvd_iff_le.mpr hIJ⟩)
    f hsum (fun v he ↦ (hprime v).ne (by rw [he, norm_one]))
  have hp' : manuscriptFiniteHeckeEuler F χ s = ∑' I, f I := by
    unfold manuscriptFiniteHeckeEuler
    apply (hp.congr_fun _).tprod_eq
    intro v
    change (1 - heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v *
      (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ =
      (1 - finiteHeckeIdealWeight F χ v.asIdeal * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹
    rw [finiteHeckeIdealWeight_prime]
  let e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 F) → ℕ)
  have hσ : Summable (fun x ↦ f (e x)) := e.summable_iff.mpr hsum.of_norm
  rw [hp', ← e.tsum_eq, hσ.tsum_sigma]
  have ht (n : ℕ) : (∑' I : {I : Ideal (𝓞 F) // I.absNorm = n}, f I.val) =
      LSeries.term (finiteHeckeNormCoefficient F χ) s n := by
    have hnfin : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).to_subtype
    letI : Fintype {I : Ideal (𝓞 F) // I.absNorm = n} := Fintype.ofFinite _
    by_cases hn : n = 0
    · subst n
      rw [LSeries.term_zero]
      rw [tsum_congr (g := fun _ ↦ (0 : ℂ)) (fun I ↦ ?_), tsum_zero]
      have hI : I.val = ⊥ := Ideal.absNorm_eq_zero_iff.mp I.property
      exact hI ▸ map_zero f
    · have hfibre (I : {I : Ideal (𝓞 F) // I.absNorm = n}) :
          f I.val = finiteHeckeIdealWeight F χ I.val * (n : ℂ) ^ (-s) := by
        change finiteHeckeIdealWeight F χ I.val * (I.val.absNorm : ℂ) ^ (-s) = _
        rw [I.property]
      rw [tsum_congr hfibre, tsum_mul_right, tsum_fintype, LSeries.term_of_ne_zero hn,
        Complex.cpow_neg, div_eq_mul_inv, finiteHeckeNormCoefficient, finsum_eq_sum_of_fintype]
  unfold LSeriesHasSum
  rw [← funext ht]
  exact hσ.sigma.hasSum

open scoped nonZeroDivisors

/-- The number of nonzero ideals of a fixed norm. -/
def finiteHeckeNormMultiplicity (n : ℕ) : ℝ :=
  if n = 0 then 0 else Nat.card {I : Ideal (𝓞 F) // I.absNorm = n}

theorem finiteHeckeNormMultiplicity_nonneg (n : ℕ) :
    0 ≤ finiteHeckeNormMultiplicity F n := by
  unfold finiteHeckeNormMultiplicity
  split <;> positivity

@[simp] theorem finiteHeckeNormCoefficient_zero (χ : PontryaginDual (IdeleClass F)) :
    finiteHeckeNormCoefficient F χ 0 = 0 := by
  unfold finiteHeckeNormCoefficient
  apply finsum_eq_zero_of_forall_eq_zero
  intro I
  have hI : I.val = ⊥ := Ideal.absNorm_eq_zero_iff.mp I.property
  simp [hI, finiteHeckeIdealWeight]

theorem finiteHeckeNormCoefficient_one (n : ℕ) :
    finiteHeckeNormCoefficient F 1 n = (finiteHeckeNormMultiplicity F n : ℂ) := by
  classical
  by_cases hn : n = 0
  · simp [hn, finiteHeckeNormMultiplicity]
  have : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).to_subtype
  letI : Fintype {I : Ideal (𝓞 F) // I.absNorm = n} := Fintype.ofFinite _
  have he (I : {I : Ideal (𝓞 F) // I.absNorm = n}) : I.val ≠ ⊥ := by
    intro h
    exact hn (I.property.symm.trans (Ideal.absNorm_eq_zero_iff.mpr h))
  simp only [finiteHeckeNormCoefficient, finiteHeckeNormMultiplicity, hn, ite_false,
    finsum_eq_sum_of_fintype, finiteHeckeIdealWeight_one _ _ (he _)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

theorem norm_finiteHeckeNormCoefficient_le (χ : PontryaginDual (IdeleClass F)) (n : ℕ) :
    ‖finiteHeckeNormCoefficient F χ n‖ ≤ finiteHeckeNormMultiplicity F n := by
  classical
  by_cases hn : n = 0
  · simp [hn, finiteHeckeNormMultiplicity]
  have : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).to_subtype
  letI : Fintype {I : Ideal (𝓞 F) // I.absNorm = n} := Fintype.ofFinite _
  rw [finiteHeckeNormCoefficient, finiteHeckeNormMultiplicity, ite_eq_right hn,
    finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  exact (norm_sum_le _ _).trans (by
    simpa using Finset.sum_le_sum
      (s := Finset.univ) (fun (I : {I : Ideal (𝓞 F) // I.absNorm = n}) _ ↦
        norm_finiteHeckeIdealWeight_le_one F χ I.val))

private abbrev BoundedIdeals (n : ℕ) := {I : Ideal (𝓞 F) // I.absNorm ≤ n}

private def normFibreEquiv (n : ℕ) :
    (Σ k : ↥(Finset.Icc 0 n), {I : Ideal (𝓞 F) // I.absNorm = k.val}) ≃ BoundedIdeals F n where
  toFun k := ⟨k.2.val, k.2.property.le.trans (Finset.mem_Icc.mp k.1.property).2⟩
  invFun I := ⟨⟨I.val.absNorm, Finset.mem_Icc.mpr ⟨Nat.zero_le _, I.property⟩⟩, I.val, rfl⟩
  left_inv := by
    rintro ⟨k, I⟩
    apply Sigma.ext (Subtype.ext I.property)
    refine (Subtype.heq_iff_coe_eq (fun J ↦ ?_)).mpr rfl
    change J.absNorm = I.val.absNorm ↔ J.absNorm = k.val
    rw [I.property]
  right_inv _ := rfl

/-- Group the actual ideal sum by its finitely many integral norm fibres. -/
theorem finiteHeckeIdealSummatory_eq_sum (χ : PontryaginDual (IdeleClass F)) (x : ℝ)
    (hx : 0 ≤ x) :
    finiteHeckeIdealSummatory F χ x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, finiteHeckeNormCoefficient F χ n := by
  classical
  let N := ⌊x⌋₊
  let V := BoundedIdeals F N
  let U := {I : nonZeroDivisors (Ideal (𝓞 F)) // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x}
  let j : U → V := fun I ↦ ⟨I.val.val, (Nat.le_floor_iff hx).mpr I.property⟩
  have hV : Finite V := (Ideal.finite_setOfPred_absNorm_le N).to_subtype
  letI : Fintype V := Fintype.ofFinite _
  have hj : Injective j := fun i j h ↦ Subtype.ext (Subtype.ext
    (congrArg (fun k : V ↦ k.val) h))
  letI : Finite U := Finite.of_injective j hj
  letI : Fintype U := Fintype.ofFinite _
  have hf (I : V) (hI : I ∉ range j) : finiteHeckeIdealWeight F χ I.val = 0 := by
    have hi : I.val = ⊥ := by
      by_contra hn
      apply hI
      refine ⟨⟨⟨I.val, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, ?_⟩, rfl⟩
      exact (Nat.le_floor_iff hx).mp I.property
    simp [hi, finiteHeckeIdealWeight]
  let W (k : ↥(Finset.Icc 0 N)) := {I : Ideal (𝓞 F) // I.absNorm = k.val}
  letI (k : ↥(Finset.Icc 0 N)) : Fintype (W k) :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) k.val).fintype
  calc
    finiteHeckeIdealSummatory F χ x = ∑ I : U, finiteHeckeIdealWeight F χ (j I).val := by
      unfold finiteHeckeIdealSummatory
      exact finsum_eq_sum_of_fintype _
    _ = ∑ I : V, finiteHeckeIdealWeight F χ I.val := by
      refine Fintype.sum_of_injective j hj _ _ ?_ (fun _ ↦ rfl)
      exact fun i hi ↦ hf i hi
    _ = ∑ k : (Σ k, W k), finiteHeckeIdealWeight F χ k.2.val := by
      exact (Equiv.sum_comp (normFibreEquiv F N) _).symm
    _ = ∑ n ∈ Finset.Icc 0 N, finiteHeckeNormCoefficient F χ n := by
      rw [Fintype.sum_sigma]
      trans ∑ n : ↥(Finset.Icc 0 N), finiteHeckeNormCoefficient F χ n.val
      · refine Finset.sum_congr rfl fun n _ ↦ ?_
        exact (finsum_eq_sum_of_fintype _).symm
      · exact Finset.sum_attach _ _

end
end Masullo
