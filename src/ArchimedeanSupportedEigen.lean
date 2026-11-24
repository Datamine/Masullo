import HeckeTensorFactors
import RealSchwartzBorelJets
import ComplexSchwartzPointJets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Function Set Topology
open scoped Classical ContDiff SchwartzMap

namespace Masullo

noncomputable section

/-- A real jet transforms by the inverse unit to the power of its order. -/
theorem realSchwartzJet_archDilation (n : ℕ) (u : ℝˣ) (f : 𝓢(ℝ, ℂ)) :
    realSchwartzJet n (archSchwartzDilation u f) =
      (↑(u⁻¹ : ℝˣ).val : ℂ) ^ n * realSchwartzJet n f := by
  let r : ℝ := (u⁻¹ : ℝˣ).val
  have he : (⇑(archSchwartzDilation u f) : ℝ → ℂ) = fun x => f (r * x) := by
    funext x
    rw [archSchwartzDilation_apply, mul_comm]
  rw [realSchwartzJet_apply, he]
  have htop : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  change iteratedDeriv n (fun x => f.toFun (r * x)) 0 = _
  rw [iteratedDeriv_comp_const_smul (f.smooth'.of_le htop) r]
  change r ^ n • iteratedDeriv n (f : ℝ → ℂ) (r * 0) = _
  rw [mul_zero, Complex.real_smul, Complex.ofReal_pow, realSchwartzJet_apply]

private theorem real_weight_eq_jet_exponent (a n : ℕ) (z : ℂ)
    (h : ∀ u : ℝˣ, realArchUnitWeight a z u = (↑(u⁻¹ : ℝˣ).val : ℂ) ^ n) :
    z = -(n : ℂ) := by
  have he (t : ℝ) : Complex.exp ((t : ℂ) * z) = Complex.exp ((t : ℂ) * -(n : ℂ)) := by
    let u := Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
    have hh := h u
    have hpos : (0 : ℝ) < u.val := Real.exp_pos t
    rw [realArchUnitWeight, abs_of_pos hpos, ite_eq_right (not_lt_of_ge hpos.le), mul_one,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, Units.val_inv_eq_inv_val] at hh
    change Complex.exp ((Real.log (Real.exp t) : ℂ) * z) = (↑((Real.exp t)⁻¹) : ℂ) ^ n at hh
    rw [Real.log_exp, ← Complex.ofReal_pow, ← Real.exp_neg, ← Real.exp_nat_mul,
      Complex.ofReal_exp] at hh
    convert hh using 2
    push_cast
    ring
  have hd (s : ℂ) : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * s)) s 0 := by
    simpa using ((Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt.mul_const s).cexp
  exact (hd z).unique ((funext he).symm ▸ hd (-(n : ℂ)))

/-- Every nonzero real tempered eigendistribution supported at the origin
is a single jet. Its exponent and sign character must match that jet. -/
theorem realSupportedWeilEigen_eq_jet (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {0}) (hT₀ : T ≠ 0) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f) :
    ∃ (n : ℕ) (b : ℂ), b ≠ 0 ∧ z = -(n : ℂ) ∧
      (-1 : ℂ) ^ a = (-1 : ℂ) ^ n ∧ T = b • realSchwartzJet n := by
  obtain ⟨N, c, hc⟩ := pointTemperedDistribution_eq_sum_of_dsupport T hT
  have hchar (i : Fin (N + 1)) (hi : c i ≠ 0) (u : ℝˣ) :
      realArchUnitWeight a z u = (↑(u⁻¹ : ℝˣ).val : ℂ) ^ i.val := by
    obtain ⟨f, hf⟩ := exists_realSchwartz_with_jets (fun n => if n = i.val then 1 else 0)
    have hbase : T f = c i := by
      rw [hc f, Finset.sum_eq_single i, hf, ite_eq_left rfl, mul_one]
      · intro j _ hj
        rw [hf, ite_eq_right (fun h => hj (Fin.ext h)), mul_zero]
      · simp
    have hscale : T (archSchwartzDilation u f) = c i * (↑(u⁻¹ : ℝˣ).val : ℂ) ^ i.val := by
      rw [hc, Finset.sum_eq_single i, realSchwartzJet_archDilation, hf, ite_eq_left rfl, mul_one]
      · intro j _ hj
        rw [realSchwartzJet_archDilation, hf, ite_eq_right (fun h => hj (Fin.ext h)), mul_zero, mul_zero]
      · simp
    have he := hcov u f
    rw [hbase, hscale, mul_comm (c i)] at he
    exact (mul_right_cancel₀ hi he).symm
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! h
    apply hT₀
    ext f
    rw [hc]
    simp [h]
  have hz := real_weight_eq_jet_exponent a i.val z (hchar i hi)
  have hsign : (-1 : ℂ) ^ a = (-1 : ℂ) ^ i.val := by
    have he := hchar i hi (-1 : ℝˣ)
    simpa [realArchUnitWeight] using he
  refine ⟨i.val, c i, hi, hz, hsign, ?_⟩
  ext f
  rw [hc, Finset.sum_eq_single i]
  · rfl
  · intro j _ hj
    have hn : c j = 0 := by
      by_contra hne
      have h₂ := real_weight_eq_jet_exponent a j.val z (hchar j hne)
      apply hj
      apply Fin.ext
      have h : (j.val : ℂ) = i.val := neg_injective (h₂.symm.trans hz)
      exact_mod_cast h
    rw [hn, zero_mul]
  · simp

/-- The jets at the origin do realize every one of the supported real
eigenweights allowed by the exponent and the sign character. -/
theorem realSupportedWeilEigen_exists_iff (a : ℕ) (z : ℂ) :
    (∃ T : StrongDual ℂ 𝓢(ℝ, ℂ), T ≠ 0 ∧ Distribution.dsupport (⇑T) ⊆ {0} ∧
      ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f) ↔
      ∃ n : ℕ, z = -(n : ℂ) ∧ (-1 : ℂ) ^ a = (-1 : ℂ) ^ n := by
  constructor
  · rintro ⟨T, hne, hs, he⟩
    obtain ⟨n, _, _, hz, hparity, _⟩ := realSupportedWeilEigen_eq_jet T hs hne a z he
    exact ⟨n, hz, hparity⟩
  · rintro ⟨n, rfl, hparity⟩
    refine ⟨realSchwartzJet n, ?_, ?_, ?_⟩
    · obtain ⟨f, hf⟩ := exists_realSchwartz_with_jets (fun _ => 1)
      intro h
      have he : realSchwartzJet n f = 0 := DFunLike.congr_fun h f
      exact one_ne_zero ((hf n).symm.trans he)
    · intro x hx
      apply (Distribution.mem_dsupport_iff x).mp hx {0} _ isClosed_singleton
      intro f hf
      have hloc : (f : ℝ → ℂ) =ᶠ[𝓝 0] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hf h rfl)
      rw [realSchwartzJet_apply, hloc.iteratedDeriv_eq]
      simp
    · intro u f
      rw [realSchwartzJet_archDilation]
      congr 1
      rw [realArchUnitWeight, Complex.cpow_neg, Complex.cpow_natCast,
        Units.val_inv_eq_inv_val, Complex.ofReal_inv, ← inv_pow]
      rcases lt_or_gt_of_ne u.ne_zero with hu | hu
      · have he : (↑(u : ℝ) : ℂ) = (-1 : ℂ) * (|(u : ℝ)| : ℝ) := by
          rw [neg_one_mul, ← Complex.ofReal_neg, abs_of_neg hu, neg_neg]
        rw [he, mul_inv, mul_pow, ite_eq_left hu, hparity, inv_neg, inv_one, mul_comm]
      · rw [abs_of_pos hu, ite_eq_right (not_lt_of_ge hu.le), mul_one]

private theorem normalized_map_eq_smul_of_ker {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] (L J : V →L[ℂ] ℂ) (g : V) (hg : L g = 1)
    (hk : ∀ f, J f = 0 → L f = 0) :
    J g ≠ 0 ∧ L = (J g)⁻¹ • J := by
  have hne : J g ≠ 0 := fun hz => one_ne_zero (hg.symm.trans (hk g hz))
  refine ⟨hne, ?_⟩
  ext f
  have he := hk (J g • f - J f • g) (by
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [mul_comm, sub_self])
  simp only [map_sub, map_smul, smul_eq_mul, hg, mul_one, sub_eq_zero] at he
  change L f = (J g)⁻¹ * J f
  rw [← he, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- At every real reciprocal-Gamma zero the normalized distribution is the
matching derivative jet divided by that jet on the reference Gaussian. -/
theorem realWeilNormalizedFamily_eq_jet (a n : ℕ) (hn : Even (a + n)) :
    let g := (realGammaNormalized_distribution a).choose
    realSchwartzJet n g ≠ 0 ∧
      realWeilNormalizedFamily a (-(n : ℂ)) =
        (realSchwartzJet n g)⁻¹ • realSchwartzJet n := by
  intro g
  have hg : realWeilNormalizedFamily a (-(n : ℂ)) g = 1 :=
    (realGammaNormalized_distribution a).choose_spec.choose_spec.2.2.1 _
  apply normalized_map_eq_smul_of_ker _ _ g hg
  intro f hf
  have ha := realArchimedeanZetaContinued_order a n f
  rw [realSchwartzJet_apply] at hf
  rw [hf, mul_zero, mul_zero, ite_eq_left rfl] at ha
  have hD : realArchZetaDenominator a (-(n : ℂ)) = 0 := by
    apply inv_eq_zero.mpr
    by_contra hne
    have hreg := (realArchZetaRegular_iff_gamma a (-(n : ℂ))).mpr hne
    exact (Nat.not_odd_iff_even.mpr hn) (hreg n (neg_add_cancel _))
  rw [← realWeilNormalizedFamily_of_analyticAt a f _ ha, hD, zero_mul]

/-- At each complex reciprocal-Gamma zero the normalized distribution is
the matching mixed Wirtinger jet divided by its value on the angular Gaussian. -/
theorem complexWeilNormalizedFamily_eq_jet (a b : ℕ) :
    let m : ℤ := (b : ℤ) - a
    let g := (complexGammaNormalized_distribution m).choose
    complexSchwartzPointJet a b g ≠ 0 ∧
      complexWeilNormalizedFamily m (-((a + b : ℕ) : ℂ) / 2) =
        (complexSchwartzPointJet a b g)⁻¹ • complexSchwartzPointJet a b := by
  intro m g
  let k := a + b
  let z : ℂ := -(k : ℂ) / 2
  have hg : complexWeilNormalizedFamily m z g = 1 :=
    (complexGammaNormalized_distribution m).choose_spec.choose_spec.2.2.1 _
  apply normalized_map_eq_smul_of_ker _ _ g hg
  intro f hf
  have hcoeff : mellinTaylorCoeff (complexZetaProfile complexTamagawaAngularMeasure m f) k = 0 := by
    rw [complexZetaProfile_taylorCoeff]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with h
    · have he : j = a := by dsimp [m, k] at h; omega
      subst j
      rw [complexAngularPolynomial_coeff_wirtinger k a (by dsimp [k]; omega)]
      rw [show k - a = b by dsimp [k]; omega]
      change _ * (_ * complexSchwartzPointJet a b f) = 0
      rw [hf, mul_zero, mul_zero]
    · rfl
  have ha : AnalyticAt ℂ (complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f) z :=
    by
      have h := complexArchimedeanZetaContinued_order complexTamagawaAngularMeasure m f k
      rwa [ite_eq_left hcoeff] at h
  have hD : complexArchZetaDenominator m z = 0 := by
    apply inv_eq_zero.mpr
    by_contra hne
    have hreg := (complexArchZetaRegular_iff_gamma m z).mpr hne
    have hzero : 2 * z + (k : ℂ) = 0 := by dsimp [z]; ring
    refine hreg k hzero ⟨min a b, ?_⟩
    dsimp [k, m]
    omega
  rw [← complexWeilNormalizedFamily_of_analyticAt m f z ha, hD, zero_mul]

/-- Every zero of the complex reciprocal Gamma factor has an exceptional
Wirtinger value with the indices determined by the angular character. -/
theorem complexWeilNormalizedFamily_eq_jet_of_denominator_zero (m : ℤ) (z : ℂ)
    (hD : complexArchZetaDenominator m z = 0) :
    ∃ a b : ℕ, (b : ℤ) - a = m ∧ z = -((a + b : ℕ) : ℂ) / 2 ∧
      let g := (complexGammaNormalized_distribution m).choose
      complexSchwartzPointJet a b g ≠ 0 ∧
        complexWeilNormalizedFamily m z =
          (complexSchwartzPointJet a b g)⁻¹ • complexSchwartzPointJet a b := by
  have hreg : ¬ ComplexArchZetaRegular m z := by
    intro h
    exact inv_ne_zero ((complexArchZetaRegular_iff_gamma m z).mp h) hD
  unfold ComplexArchZetaRegular at hreg
  push Not at hreg
  obtain ⟨k, hk, n, hn⟩ := hreg
  let a := (-m).toNat + n
  let b := m.toNat + n
  have hm : (b : ℤ) - a = m := by dsimp [a, b]; omega
  have hab : a + b = k := by dsimp [a, b]; omega
  have hz : z = -((a + b : ℕ) : ℂ) / 2 := by rw [hab]; linear_combination hk / 2
  refine ⟨a, b, hm, hz, ?_⟩
  rw [hz, ← hm]
  exact complexWeilNormalizedFamily_eq_jet a b

/-- Every nonzero real eigendistribution supported at zero is a multiple of
the Gaussian-normalized family at its parameter. -/
theorem realSupportedWeilEigen_eq_normalized (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {0}) (hT₀ : T ≠ 0) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f) :
    ∃ b : ℂ, b ≠ 0 ∧ T = b • realWeilNormalizedFamily a z := by
  obtain ⟨n, b, hb, rfl, hs, hTj⟩ := realSupportedWeilEigen_eq_jet T hT hT₀ a z hcov
  have he : Even (a + n) := by
    apply (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp
    rw [pow_add, hs, ← pow_add, ← two_mul, pow_mul]
    norm_num
  let g := (realGammaNormalized_distribution a).choose
  have hjet : realSchwartzJet n g ≠ 0 ∧
      realWeilNormalizedFamily a (-(n : ℂ)) =
        (realSchwartzJet n g)⁻¹ • realSchwartzJet n :=
    realWeilNormalizedFamily_eq_jet a n he
  refine ⟨b * realSchwartzJet n g, mul_ne_zero hb hjet.1, ?_⟩
  rw [hTj, hjet.2, smul_smul, mul_assoc, mul_inv_cancel₀ hjet.1, mul_one]

/-- The complex normalized family is supported at zero at every reciprocal
Gamma zero. -/
theorem complexWeilNormalizedFamily_support_of_denominator_zero (m : ℤ) (z : ℂ)
    (hD : complexArchZetaDenominator m z = 0) :
    Distribution.dsupport (⇑(complexWeilNormalizedFamily m z)) ⊆ {0} := by
  obtain ⟨a, b, _, _, _, he⟩ := complexWeilNormalizedFamily_eq_jet_of_denominator_zero m z hD
  rw [he]
  intro x hx
  apply (Distribution.mem_dsupport_iff x).mp hx {0} _ isClosed_singleton
  intro f hf
  have hloc : (f : ℂ → ℂ) =ᶠ[𝓝 0] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => hf h rfl)
  have hjet : complexSchwartzPointJet a b f = 0 := by
    apply (complexSchwartzPointJet_vanishing_iff (a + b) f).mpr _ a b le_rfl
    intro k _
    rw [(hloc.iteratedFDeriv ℝ k).eq_of_nhds]
    simp
  change _ * complexSchwartzPointJet a b f = 0
  rw [hjet, mul_zero]

end

end Masullo
