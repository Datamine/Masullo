import GlobalOrbitalMarkushevich
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.Analysis.PSeries

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical FourierTransform InnerProductSpace NumberField SchwartzMap

namespace Masullo
noncomputable section

section Periodic

variable (M : ℝ → ℕ) {d : ℝ}

/-- The moment labels in one half-open cell of a periodic multiplicity function. -/
def periodicMomentCell (d : ℝ) : Set (ℝ × ℕ) :=
  {i | i.1 ∈ Ico 0 d ∧ i.2 < M i.1}

private theorem periodicMoment_normalize (hd : 0 < d) (hM : Periodic M d) (i : ℝ × ℕ)
    (hi : i.2 < M i.1) :
    ∃ j : periodicMomentCell M d × ℤ, (j.1.val.1 + (j.2 : ℝ) * d,j.1.val.2) = i := by
  obtain ⟨n, hn⟩ := exists_integerTranslate_mem_Ico 0 hd i.1
  have he := (hM.int_mul n) i.1
  refine ⟨(⟨(i.1 + (n : ℝ)*d,i.2), ⟨?_, ?_⟩⟩,-n), ?_⟩
  · simpa only [mul_comm (n : ℝ), zero_add] using hn
  · simpa only [he] using hi
  · apply Prod.ext
    · simp only [Int.cast_neg]; ring
    · rfl

private theorem periodicMoment_unique (hd : 0 < d)
    {x y : ℝ} (hx : x ∈ Ico 0 d) (hy : y ∈ Ico 0 d) {m n : ℤ}
    (he : x + (m : ℝ)*d = y + (n : ℝ)*d) : x = y ∧ m = n := by
  have hlt (a b : ℝ) (ha : a < d) (hb : 0 ≤ b) (j k : ℤ) (h : j < k) :
      a + (j : ℝ)*d < b + (k : ℝ)*d := by
    have h' : (j : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast (show j+1 ≤ k by omega)
    have h'' := mul_le_mul_of_nonneg_right h' hd.le
    rw [add_mul, one_mul] at h''
    linarith
  have hmn : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · exact (ne_of_lt (hlt x y hx.2 hy.1 m n h) he).elim
    · exact h
    · exact (ne_of_lt (hlt y x hy.2 hx.1 n m h) he.symm).elim
  exact ⟨add_right_cancel (hmn ▸ he),hmn⟩

/-- Each moment has a unique label given by its cell representative and integer translate. -/
def periodicMomentEquiv (hd : 0 < d) (hM : Periodic M d) :
    (periodicMomentCell M d × ℤ) ≃ {i : ℝ × ℕ | i.2 < M i.1} :=
  Equiv.ofBijective (fun j ↦ ⟨(j.1.val.1 + (j.2 : ℝ)*d,j.1.val.2),
    by
      change j.1.val.2 < M (j.1.val.1 + (j.2 : ℝ)*d)
      rw [(hM.int_mul j.2) j.1.val.1]
      exact j.1.property.2⟩) (by
        constructor
        · intro a b h
          have hx := congrArg (fun i : {i : ℝ × ℕ | i.2 < M i.1} ↦ i.val.1) h
          have hj := congrArg (fun i : {i : ℝ × ℕ | i.2 < M i.1} ↦ i.val.2) h
          obtain ⟨he, hn⟩ := periodicMoment_unique hd a.1.property.1 b.1.property.1 hx
          exact Prod.ext (Subtype.ext (Prod.ext he hj)) hn
        · intro i
          obtain ⟨j,hj⟩ := periodicMoment_normalize M hd hM i.val i.property
          exact ⟨j,Subtype.ext hj⟩)


private theorem summable_int_inverse_one_add_sq :
    Summable (fun n : ℤ ↦ (1 + (n : ℝ)^2)⁻¹) := by
  let v : ℤ → ℝ := fun n ↦ if n = 0 then 1 else 0
  have hv : Summable v := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro n hn
    have hne : n ≠ 0 := fun h ↦ hn (h ▸ Finset.mem_singleton_self _)
    simp [v,hne]
  have hs : Summable (fun n : ℤ ↦ ((n : ℝ)^2)⁻¹) := by
    simpa only [one_div] using (Real.summable_one_div_int_pow (p := 2)).mpr (by decide)
  refine (hs.add hv).of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
  by_cases hn : n = 0
  · simp [hn, v]
  · have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    simp only [v, ite_eq_right hn, add_zero]
    exact inv_anti₀ (sq_pos_of_ne_zero hn') (le_add_of_nonneg_left zero_le_one)

/-- Sampling on any translate in a fixed half-open cell is summable, with one
continuous two-seminorm bound for the whole cell. -/
theorem schwartz_samples_periodic_bound (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ), a ∈ Ico 0 d → ∀ f : 𝓢(ℝ, ℂ),
      Summable (fun n : ℤ ↦ ‖f (a + (n : ℝ)*d)‖) ∧
      (∑' n : ℤ, ‖f (a + (n : ℝ)*d)‖) ≤
        C * (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ 2 0 f) := by
  let w (n : ℤ) : ℝ := (1 + (n : ℝ)^2)⁻¹
  have hw : Summable w := summable_int_inverse_one_add_sq
  let D := 3 + 2/d^2
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 0 < ∑' n : ℤ, w n := by
    have hle := hw.le_tsum (0 : ℤ) (fun i _ ↦ by dsimp [w]; positivity)
    exact lt_of_lt_of_le (by norm_num [w]) hle
  refine ⟨D * (∑' n : ℤ, w n), mul_pos hD hW, fun a ha f ↦ ?_⟩
  let P := SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ 2 0 f
  have hP : 0 ≤ P := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hbound (n : ℤ) : ‖f (a + (n : ℝ)*d)‖ ≤ (D*P) * w n := by
    let x := a + (n : ℝ)*d
    have h0 : ‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := by
      simpa using SchwartzMap.norm_pow_mul_le_seminorm ℂ f 0 x
    have h2 : x^2 * ‖f x‖ ≤ SchwartzMap.seminorm ℂ 2 0 f := by
      simpa only [Real.norm_eq_abs, sq_abs] using SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 x
    have hf : (1+x^2) * ‖f x‖ ≤ P := by rw [add_mul, one_mul]; exact add_le_add h0 h2
    have he : (n : ℝ)^2 * d^2 = (x-a)^2 := by dsimp [x]; ring
    have haa : a^2 ≤ d^2 := pow_le_pow_left₀ ha.1 ha.2.le _
    have hnd : (n : ℝ)^2 * d^2 ≤ 2*x^2 + 2*d^2 := by
      rw [he]
      nlinarith [sq_nonneg (x+a)]
    have hn : 1+(n : ℝ)^2 ≤ D * (1+x^2) := by
      apply (le_of_mul_le_mul_right (a := d^2) · (by positivity : 0 < d^2))
      dsimp only [D]
      field_simp
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg d)]
    change ‖f x‖ ≤ D * P * w n
    rw [show w n = 1/(1+(n : ℝ)^2) by simp [w,one_div], mul_one_div,
      le_div_iff₀ (by positivity)]
    calc
      _ ≤ (D * (1+x^2)) * ‖f x‖ := by
        rw [mul_comm ‖f x‖]
        exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = D * ((1+x^2) * ‖f x‖) := mul_assoc _ _ _
      _ ≤ D * P := mul_le_mul_of_nonneg_left hf hD.le
  have hs := hw.mul_left (D*P)
  have hf := hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  refine ⟨hf, (hf.tsum_le_tsum hbound hs).trans_eq ?_⟩
  rw [tsum_mul_left]
  ring

end Periodic

section Global

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I

/-- A set of places above one rational prime has cardinality at most the field degree. -/
theorem globalPrimaryPlaces_card_le_degree (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)}) :
    A.card ≤ Module.finrank ℚ F := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hp₀ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hP₀ : P ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hp₀
  have hP : P.IsPrime := (Ideal.span_singleton_prime hp₀).mpr (Nat.prime_iff_prime_int.mp hp)
  letI : P.IsMaximal := hP.isMaximal hP₀
  apply (Finset.card_le_card_of_injOn (fun v : Place F ↦ v.asIdeal)
    (t := IsDedekindDomain.primesOverFinset P (𝓞 F)) ?_ ?_).trans
    (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hP₀)
  · intro v hv
    exact (IsDedekindDomain.mem_primesOverFinset_iff hP₀ (𝓞 F)).mpr
      ⟨v.isPrime, ⟨(hA v hv).symm⟩⟩
  · exact HeightOneSpectrum.asIdeal_injective.injOn

/-- In the real Fourier-frequency coordinate the common period above p is the
reciprocal of log p. -/
def primaryOrbitalFrequencyPeriod (p : ℕ) : ℝ := (Real.log (p : ℝ))⁻¹

theorem primaryOrbitalFrequencyPeriod_pos {p : ℕ} (hp : p.Prime) :
    0 < primaryOrbitalFrequencyPeriod p :=
  inv_pos.mpr (Real.log_pos (by exact_mod_cast hp.one_lt))

private theorem primePeriod_log_absNorm {p : ℕ} (hp : p.Prime) (v : Place F)
    (hv : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)}) :
    primaryOrbitalFrequencyPeriod p * Real.log (v.asIdeal.absNorm : ℝ) =
      ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : ℝ) := by
  letI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hv.symm⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
  rw [h, Nat.cast_pow, Real.log_pow, primaryOrbitalFrequencyPeriod]
  have hp0 := (Real.log_pos (show 1 < (p : ℝ) by exact_mod_cast hp.one_lt)).ne'
  field_simp

private theorem orbitalPhase_periodic {p : ℕ} (hp : p.Prime) (v : Place F)
    (hv : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (χ : PontryaginDual (IdeleClass F)) :
    Periodic (fun ξ ↦ orbitalMomentPhase F χ (zAt ξ) (globalUniformizerClass F v))
      (primaryOrbitalFrequencyPeriod p) := by
  let d := primaryOrbitalFrequencyPeriod p
  let L := Real.log (v.asIdeal.absNorm : ℝ)
  let n := (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal
  have hn : (d : ℂ) * (L : ℂ) = (n : ℂ) := by exact_mod_cast primePeriod_log_absNorm F hp v hv
  have hlog : (ideleClassLogNorm F (globalUniformizerClass F v)).toAdd = -L := by
    change Real.log (ideleClassNorm F (ideleClassMap F
      (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) = -L
    rw [ideleClassNorm_mk, singleFiniteIdele_norm,
      norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv]
  intro ξ
  let g := globalUniformizerClass F v
  change ((χ g : ℂ) * Complex.exp (zAt (ξ+d) * ((ideleClassLogNorm F g).toAdd : ℂ))) =
    (χ g : ℂ) * Complex.exp (zAt ξ * ((ideleClassLogNorm F g).toAdd : ℂ))
  rw [show (ideleClassLogNorm F g).toAdd = -L from hlog]
  have hArg : zAt (ξ+d) * ((-L : ℝ) : ℂ) =
      zAt ξ * ((-L : ℝ) : ℂ) + (n : ℤ) * (2*(Real.pi : ℂ)*Complex.I) := by
    simp only [zAt]
    push_cast
    linear_combination (2*(Real.pi : ℂ)*Complex.I) * hn
  rw [hArg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Above a single rational prime the actual global Weil multiplicities are periodic,
including coincidences between different local factors. -/
theorem globalWeilMomentMultiplicity_primary_periodic (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (ω : PontryaginDual (K F)) :
    Periodic (fun ξ ↦ globalWeilMomentMultiplicity F A ω (normOneEulerCharacter F ω) (zAt ξ))
      (primaryOrbitalFrequencyPeriod p) := by
  intro ξ
  change globalWeilMomentMultiplicity F A ω (normOneEulerCharacter F ω)
      (zAt (ξ+primaryOrbitalFrequencyPeriod p)) =
    globalWeilMomentMultiplicity F A ω (normOneEulerCharacter F ω) (zAt ξ)
  unfold globalWeilMomentMultiplicity
  congr 1
  apply Finset.filter_congr
  intro v hv
  change (_ ∧ orbitalMomentPhase F (normOneEulerCharacter F ω)
      (zAt (ξ+primaryOrbitalFrequencyPeriod p)) (globalUniformizerClass F v) = 1) ↔
    (_ ∧ orbitalMomentPhase F (normOneEulerCharacter F ω) (zAt ξ) (globalUniformizerClass F v) = 1)
  have he := orbitalPhase_periodic F hp v (hA v hv) (normOneEulerCharacter F ω) ξ
  change orbitalMomentPhase F (normOneEulerCharacter F ω)
      (zAt (ξ+primaryOrbitalFrequencyPeriod p)) (globalUniformizerClass F v) =
    orbitalMomentPhase F (normOneEulerCharacter F ω) (zAt ξ) (globalUniformizerClass F v) at he
  rw [he]


private abbrev canonicalMultiplicity (A : Finset (Place F)) (ω : PontryaginDual (K F)) (ξ : ℝ) :=
  globalWeilMomentMultiplicity F A ω (normOneEulerCharacter F ω) (zAt ξ)

/-- Each compact interval carries only finitely many of the actual global moments. -/
theorem globalWeilMomentIndices_finite_in_compact (A : Finset (Place F))
    (ω : PontryaginDual (K F)) (B : Set ℝ) (hB : IsCompact B) :
    {i | i.1 ∈ B ∧ i ∈ globalWeilMomentIndices F A ω}.Finite := by
  letI : MeasurableSpace (K F) := borel _
  letI : BorelSpace (K F) := ⟨rfl⟩
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  obtain ⟨ds, hd, _, hm⟩ := exists_globalZeroLineWeil_shiftModel F Measure.haar 0 le_rfl A ω
  apply (radialWeilProduct_finite_moment_indices ds hd B hB).subset
  intro i hi
  change i.1 ∈ B ∧ i.2 < canonicalMultiplicity F A ω i.1 at hi
  change i.1 ∈ B ∧ i.2 < ds.countP _
  rw [hm]
  exact hi

/-- The primary labels form a finite cell times the integers. -/
theorem exists_globalPrimaryMoment_index (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (ω : PontryaginDual (K F)) :
    let d := primaryOrbitalFrequencyPeriod p
    let J := periodicMomentCell (canonicalMultiplicity F A ω) d
    J.Finite ∧
      ∃ e : (J × ℤ) ≃ globalWeilMomentIndices F A ω,
        ∀ j, (e j).val = (j.1.val.1 + (j.2 : ℝ) * d, j.1.val.2) := by
  intro d J
  have hJ : J.Finite := (globalWeilMomentIndices_finite_in_compact F A ω (Icc 0 d)
    isCompact_Icc).subset (fun _ h ↦ ⟨Ico_subset_Icc_self h.1, h.2⟩)
  exact ⟨hJ, periodicMomentEquiv (canonicalMultiplicity F A ω)
    (primaryOrbitalFrequencyPeriod_pos hp) (globalWeilMomentMultiplicity_primary_periodic F A hp hA ω),
    fun _ ↦ rfl⟩


/-- All periodic Weil moment labels admit a single continuous bound on the
absolute sum of Schwartz samples, counting each derivative label once. -/
theorem globalPrimaryMoment_samples_bound (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (ω : PontryaginDual (K F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ, ℂ),
      Summable (fun i : globalWeilMomentIndices F A ω ↦ ‖f i.val.1‖) ∧
      (∑' i : globalWeilMomentIndices F A ω, ‖f i.val.1‖) ≤
        C * (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ 2 0 f) := by
  let d := primaryOrbitalFrequencyPeriod p
  let J := periodicMomentCell (canonicalMultiplicity F A ω) d
  obtain ⟨hJ,e,he⟩ := exists_globalPrimaryMoment_index F A hp hA ω
  letI : Fintype J := hJ.fintype
  obtain ⟨C,hC,hU⟩ := schwartz_samples_periodic_bound (primaryOrbitalFrequencyPeriod_pos hp)
  let D := (1+(Fintype.card J : ℝ))*C
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun f ↦ ?_⟩
  let P := SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ 2 0 f
  let a (j : J × ℤ) := ‖f (j.1.val.1 + (j.2 : ℝ)*d)‖
  let b (i : globalWeilMomentIndices F A ω) := ‖f i.val.1‖
  have hcomp (j : J × ℤ) : b (e j) = a j := by
    change ‖f (e j).val.1‖ = _
    rw [he]
  have hrow (j : J) : Summable (fun n : ℤ ↦ a (j,n)) ∧
      (∑' n : ℤ, a (j,n)) ≤ C*P := hU j.val.1 j.property.1 f
  have ham : Summable a :=
    (summable_prod_of_nonneg (fun j ↦ norm_nonneg _)).mpr
      ⟨fun j ↦ (hrow j).1, Summable.of_finite⟩
  have hbm : Summable b := by
    apply e.summable_iff.mp
    have hEq : b ∘ e = a := funext hcomp
    rw [hEq]
    exact ham
  refine ⟨hbm, ?_⟩
  change (∑' i, b i) ≤ D * P
  calc
    _ = ∑' j, a j := (e.tsum_eq b).symm.trans (tsum_congr hcomp)
    _ = ∑ j : J, ∑' n : ℤ, a (j,n) := by rw [ham.tsum_prod, tsum_fintype]
    _ ≤ ∑ _j : J, C*P := Finset.sum_le_sum (fun j _ ↦ (hrow j).2)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [D]
      have hp : 0 ≤ C*P := mul_nonneg hC.le (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hp

private abbrev S := 𝓢(ℝ, ℂ)

private theorem inverseFourier_translate_norm (b : S) (x t : ℝ) :
    ‖𝓕⁻ (b.compSubConstCLM ℂ x) t‖ = ‖𝓕⁻ b t‖ := by
  simp_rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe]
  rw [radialSchwartz_fourier_compSubConst, norm_mul, Complex.norm_exp]
  have h : (radialFourierSlope x * ((-t : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero, one_mul]

local instance primaryMomentQMeasure : MeasurableSpace (IdeleClass F) := borel _
local instance primaryMomentQBorel : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance primaryMomentQT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance primaryMomentQLC : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance primaryMomentQSecondCountable : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance primaryMomentKMeasure : MeasurableSpace (K F) := borel _
local instance primaryMomentKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance primaryMomentKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

local instance primaryMomentSplitHaar : (globalClassMeasure F ν).IsHaarMeasure :=
  globalClassMeasure_isHaar F ν

private abbrev H (ω : PontryaginDual (K F)) :=
  globalOrbitalSobolevIsotype F (globalClassMeasure F ν) s hs ω

private theorem globalWeilSchwartzTest_inverseFourier_translate_norm
    (ω : PontryaginDual (K F)) (b : S) (x : ℝ) :
    ‖globalWeilSchwartzTest F s hs ν ω (𝓕⁻ (b.compSubConstCLM ℂ x))‖ =
      ‖globalWeilSchwartzTest F s hs ν ω (𝓕⁻ b)‖ := by
  change ‖globalZeroLineSchwartzIsotype F ν s ω⁻¹ (𝓕⁻ (b.compSubConstCLM ℂ x))‖ =
    ‖globalZeroLineSchwartzIsotype F ν s ω⁻¹ (𝓕⁻ b)‖
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ (𝓕⁻ (b.compSubConstCLM ℂ x)),
    globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ (𝓕⁻ b)] with q h₁ h₂
  rw [h₁, h₂]
  simp only [norm_mul, inverseFourier_translate_norm]

set_option maxHeartbeats 1200000 in
/-- Above one residue prime, translations of finitely many Fourier tests give
a uniformly bounded interpolation family in the actual global Hilbert isotype. -/
theorem exists_globalPrimaryMoment_bounded_interpolation_split (A : Finset (Place F))
    (hdeg : 2 * (A.card : ℝ) ≤ s)
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (ω : PontryaginDual (K F)) :
    ∃ C : ℝ, 0 < C ∧ ∃ q : globalWeilMomentIndices F A ω → H F ν s hs ω,
      (∀ i, ‖q i‖ ≤ C) ∧
      ∀ i j, ⟪globalWeilMomentRepresentative F (globalClassMeasure F ν) s hs A hdeg ω j,
        q i⟫_ℂ = if j = i then 1 else 0 := by
  let d := primaryOrbitalFrequencyPeriod p
  let J := periodicMomentCell (canonicalMultiplicity F A ω) d
  let I := globalWeilMomentIndices F A ω
  let r := globalWeilMomentRepresentative F (globalClassMeasure F ν) s hs A hdeg ω
  obtain ⟨hJ, e, he⟩ := exists_globalPrimaryMoment_index F A hp hA ω
  change J.Finite at hJ
  letI : Fintype J := hJ.fintype
  let M := canonicalMultiplicity F A ω
  have hper := globalWeilMomentMultiplicity_primary_periodic F A hp hA ω
  obtain ⟨ds, hd, _, hm⟩ := exists_globalZeroLineWeil_shiftModel F ν s hs A ω
  have hI : I = radialWeilJetIndices ds := by
    ext j
    change j.2 < M j.1 ↔ j.2 < ds.countP _
    rw [hm]
  let E := Equiv.setCongr hI
  choose b hb hcard using fun j : J ↦
    exists_radialWeilJet_frequency_interpolant ds hd (E (e (j,0)))
  let B (i : J × ℤ) := (b i.1).compSubConstCLM ℂ ((i.2 : ℝ)*d)
  have hj (i : J × ℤ) (j : I) :
      iteratedDeriv j.val.2 (B i : ℝ → ℂ) j.val.1 = if j = e i then 1 else 0 := by
    let k : I := ⟨(j.val.1-(i.2 : ℝ)*d,j.val.2), by
      have h := (hper.int_mul (-i.2)) j.val.1
      change M (j.val.1 + ((-i.2 : ℤ) : ℝ) * d) = M j.val.1 at h
      rw [Int.cast_neg, neg_mul, ← sub_eq_add_neg] at h
      change j.val.2 < M (j.val.1-(i.2 : ℝ)*d)
      rw [h]
      exact j.property⟩
    have h := hcard i.1 (E k)
    change iteratedDeriv j.val.2 (b i.1 : ℝ → ℂ) (j.val.1-(i.2 : ℝ)*d) = _ at h
    change iteratedDeriv j.val.2 (fun x ↦ b i.1 (x-(i.2 : ℝ)*d)) j.val.1 = _
    rw [iteratedDeriv_comp_sub_const]
    change iteratedDeriv j.val.2 (b i.1 : ℝ → ℂ) (j.val.1-(i.2 : ℝ)*d) = _
    rw [h]
    have heq : E k = E (e (i.1,0)) ↔ j = e i := by
      rw [E.injective.eq_iff]
      constructor
      · intro h
        have hx := congrArg (fun x : I ↦ x.val.1) h
        have hy := congrArg (fun x : I ↦ x.val.2) h
        apply Subtype.ext
        rw [he]
        apply Prod.ext
        · change j.val.1 - (i.2 : ℝ)*d = (e (i.1,0)).val.1 at hx
          rw [he] at hx
          simp only [Int.cast_zero, zero_mul, add_zero] at hx
          exact sub_eq_iff_eq_add.mp hx
        · change j.val.2 = (e (i.1,0)).val.2 at hy
          rw [he] at hy
          exact hy
      · intro h
        apply Subtype.ext
        change (j.val.1-(i.2 : ℝ)*d,j.val.2) = (e (i.1,0)).val
        rw [h, he, he]
        change (i.1.val.1 + (i.2 : ℝ)*d - (i.2 : ℝ)*d, i.1.val.2) =
          (i.1.val.1 + (0 : ℤ) * d, i.1.val.2)
        simp
    by_cases h : j = e i
    · rw [ite_eq_left h, ite_eq_left (heq.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (heq.mp h'))]
  let v (i : J × ℤ) := globalWeilJetScale F ν (e i).val •
    globalWeilSchwartzTest F s hs ν ω (𝓕⁻ (B i))
  let c (j : J) := ‖globalWeilJetScale F ν (e (j,0)).val‖ *
    ‖globalWeilSchwartzTest F s hs ν ω (𝓕⁻ (b j))‖
  let C := 1 + ∑ j : J, c j
  have hc (j : J) : 0 ≤ c j := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hC : 0 < C := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _ ↦ hc j)
  have hv (i : J × ℤ) : ‖v i‖ ≤ C := by
    change ‖globalWeilJetScale F ν (e i).val •
      globalWeilSchwartzTest F s hs ν ω (𝓕⁻ (B i))‖ ≤ C
    rw [norm_smul]
    change ‖globalWeilJetScale F ν (e i).val‖ *
      ‖globalWeilSchwartzTest F s hs ν ω (𝓕⁻ ((b i.1).compSubConstCLM ℂ _))‖ ≤ C
    rw [globalWeilSchwartzTest_inverseFourier_translate_norm]
    have hscl : globalWeilJetScale F ν (e i).val =
        globalWeilJetScale F ν (e (i.1,0)).val := by simp only [globalWeilJetScale, he]
    rw [hscl]
    exact (Finset.single_le_sum (fun j _ ↦ hc j) (Finset.mem_univ i.1)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C,hC,fun i ↦ v (e.symm i),fun i ↦ hv _,?_⟩
  intro i j
  let k := e.symm i
  have hi : e k = i := e.apply_symm_apply i
  have h := globalWeilSchwartzTest_scaled_inner_eq_jet F s hs ν A hdeg ω j (𝓕⁻ (B k))
  rw [FourierTransform.fourier_fourierInv_eq, hj k j, hi] at h
  calc
    ⟪r j,v k⟫_ℂ = globalWeilJetScale F ν (e k).val *
        ⟪r j,globalWeilSchwartzTest F s hs ν ω (𝓕⁻ (B k))⟫_ℂ :=
      inner_smul_right (r j) _ _
    _ = _ := by
      by_cases hj : j = i
      · subst j
        rw [hi]
        exact h
      · rw [ite_eq_right hj] at h ⊢
        exact mul_eq_zero.mpr (Or.inr ((mul_eq_zero.mp h).resolve_left
          (globalWeilJetScale_ne_zero F ν j.val)))


variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]

omit [ν.IsHaarMeasure] in
/-- Uniform interpolation holds for every normalization of Haar measure. -/
theorem exists_globalPrimaryMoment_bounded_interpolation (A : Finset (Place F))
    (hdeg : 2 * (A.card : ℝ) ≤ s)
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (ω : PontryaginDual (K F)) :
    ∃ C : ℝ, 0 < C ∧ ∃ q : globalWeilMomentIndices F A ω → globalOrbitalSobolevIsotype F μ s hs ω,
      (∀ i, ‖q i‖ ≤ C) ∧
      ∀ i j, ⟪globalWeilMomentRepresentative F μ s hs A hdeg ω j,q i⟫_ℂ =
        if j = i then 1 else 0 := by
  obtain ⟨η,hη,he⟩ := exists_globalClassMeasure_of_haar F μ
  letI : η.IsHaarMeasure := hη
  have h (σ : Measure (IdeleClass F)) [σ.IsHaarMeasure] (hσ : globalClassMeasure F η = σ) :
      ∃ C : ℝ, 0 < C ∧ ∃ q : globalWeilMomentIndices F A ω → globalOrbitalSobolevIsotype F σ s hs ω,
        (∀ i, ‖q i‖ ≤ C) ∧
        ∀ i j, ⟪globalWeilMomentRepresentative F σ s hs A hdeg ω j,q i⟫_ℂ =
          if j = i then 1 else 0 := by
    subst σ
    exact exists_globalPrimaryMoment_bounded_interpolation_split F η s hs A hdeg hp hA ω
  exact h μ he

end Global
end
end Masullo
