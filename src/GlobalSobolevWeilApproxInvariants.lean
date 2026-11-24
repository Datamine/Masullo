import GlobalSobolevWeilExtension

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField NNReal ENNReal

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance weilApproxClassMeasurable : MeasurableSpace (Q F) := borel _
local instance weilApproxClassBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance weilApproxClassLocallyCompact : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance weilApproxClassT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance weilApproxClassSecondCountable : SecondCountableTopology (Q F) :=
  ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

private abbrev hs : (0 : ℝ) ≤ 2 := by norm_num
private abbrev t (q : Q F) := (ideleClassLogNorm F q).toAdd
private abbrev A (x : ℝ) := hardySobolevAmplitude 0 0 2 x
private abbrev T (a : Q F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 2 hs a

private theorem amplitude_formula (x : ℝ) : A x = Real.sqrt (1 + x ^ 2) := by
  norm_num [A, hardySobolevAmplitude, hardySobolevWeight]

private theorem amplitude_pos (x : ℝ) : 0 < A x := by
  rw [amplitude_formula]
  positivity

private theorem exp_abs_translate_le {ε : ℝ} (he : 0 ≤ ε) (l x : ℝ) :
    |Real.exp (-ε * |x|) - Real.exp (-ε * |x - l|)| ≤
      (Real.exp (ε * |l|) - 1) * Real.exp (-ε * |x|) := by
  let a := Real.exp (-ε * |x|)
  let b := Real.exp (-ε * |x - l|)
  let c := Real.exp (ε * |l|)
  have hc : 1 ≤ c := Real.one_le_exp (by positivity)
  have hu : b ≤ c * a := by
    rw [show c * a = Real.exp (ε * |l| - ε * |x|) by unfold c a; rw [← Real.exp_add]; congr 1; ring]
    apply Real.exp_le_exp.mpr
    have h := abs_sub_abs_le_abs_sub x (x - l)
    rw [show x - (x - l) = l by ring] at h
    nlinarith [mul_le_mul_of_nonneg_left h he]
  have hd : a ≤ c * b := by
    rw [show c * b = Real.exp (ε * |l| - ε * |x - l|) by unfold c b; rw [← Real.exp_add]; congr 1; ring]
    apply Real.exp_le_exp.mpr
    have h := abs_sub_abs_le_abs_sub (x - l) x
    rw [show x - l - x = -l by ring, abs_neg] at h
    nlinarith [mul_le_mul_of_nonneg_left h he]
  change |a - b| ≤ (c - 1) * a
  by_cases h : a ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · have hba : b ≤ a := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hb := mul_le_mul_of_nonneg_left hba (sub_nonneg.mpr hc)
    nlinarith

private abbrev profile (ε x : ℝ) : ℂ := (A x * Real.exp (-ε * |x|) : ℝ)

private theorem profile_continuous (ε : ℝ) : Continuous (profile ε) := by
  change Continuous (fun x : ℝ => ((A x * Real.exp (-ε * |x|) : ℝ) : ℂ))
  simp_rw [amplitude_formula]
  fun_prop

private theorem profile_memLp {ε : ℝ} (he : 0 < ε) :
    MemLp (fun q : Q F => profile ε (t F q)) 2 μ := by
  let w (x : ℝ) := ‖profile ε x‖ ^ 2
  have hw : Continuous w := (profile_continuous ε).norm.pow 2
  have hI : Integrable w volume := by
    refine ((integrable_exp_abs_envelope ε he).const_mul (1 + 2 / ε ^ 2)).mono' hw.aestronglyMeasurable ?_
    exact .of_forall fun x => by
      have ha : 0 ≤ A x * Real.exp (-ε * |x|) := mul_nonneg (amplitude_pos x).le (Real.exp_pos _).le
      have hx : x ^ 2 ≤ (2 / ε ^ 2) * Real.exp (ε * |x|) := by
        have he' := Real.quadratic_le_exp_of_nonneg (show 0 ≤ ε * |x| by positivity)
        have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
        rw [show (ε * |x|) ^ 2 = ε ^ 2 * x ^ 2 by rw [mul_pow, hsq]] at he'
        have hh : x ^ 2 * ε ^ 2 ≤ 2 * Real.exp (ε * |x|) := by
          nlinarith [mul_nonneg he.le (abs_nonneg x)]
        calc
          x ^ 2 ≤ 2 * Real.exp (ε * |x|) / ε ^ 2 := (le_div_iff₀ (by positivity)).mpr hh
          _ = _ := by ring
      have hbound : 1 + x ^ 2 ≤ (1 + 2 / ε ^ 2) * Real.exp (ε * |x|) := by
        have hE := Real.one_le_exp (show 0 ≤ ε * |x| by positivity)
        linarith [mul_add (Real.exp (ε * |x|)) 1 (2 / ε ^ 2)]
      change ‖‖profile ε x‖ ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity), Complex.norm_real, Real.norm_of_nonneg ha,
        mul_pow, amplitude_formula, Real.sq_sqrt (by positivity)]
      calc
        _ ≤ ((1 + 2 / ε ^ 2) * Real.exp (ε * |x|)) * Real.exp (-ε * |x|) ^ 2 :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
        _ = _ := by
          have hexp : Real.exp (ε * |x|) * Real.exp (-ε * |x|) ^ 2 = Real.exp (-ε * |x|) := by
            rw [pow_two, ← mul_assoc, ← Real.exp_add, show ε * |x| + -ε * |x| = 0 by ring,
              Real.exp_zero, one_mul]
          rw [mul_assoc, hexp]
  have hl : Continuous (t F) := ideleClassLogNorm_continuous F
  obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
  have h : Integrable w (μ.map (t F)) := by
    rw [hmap]
    exact hI.smul_measure_nnreal
  apply (memLp_two_iff_integrable_sq_norm ((profile_continuous ε).comp hl).aestronglyMeasurable).2
  exact h.comp_measurable hl.measurable

private theorem log_translate (a q : Q F) : t F (a⁻¹ * q) = t F q - t F a := by
  change (ideleClassLogNorm F (a⁻¹ * q)).toAdd = _
  rw [map_mul, map_inv]
  change -t F a + t F q = _
  ring

set_option maxHeartbeats 800000 in
private theorem profile_difference {ε : ℝ} (he : 0 < ε) (a : Q F) :
    let u := (profile_memLp F μ he).toLp _
    u ≠ 0 ∧
    u ∈ globalAmbientSobolevIsotype F (1 : PontryaginDual (K F)) μ 0 0 2 hs ∧
    ‖u - T F μ a u‖ ≤ (Real.exp (ε * |t F a|) - 1) * ‖u‖ := by
  intro u
  have hu : (u : Q F → ℂ) =ᵐ[μ] fun q => profile ε (t F q) := (profile_memLp F μ he).coeFn_toLp
  have hTa (g : Q F) : (T F μ g u : Q F → ℂ) =ᵐ[μ] fun q =>
      (A (t F q) * Real.exp (-ε * |t F q - t F g|) : ℝ) := by
    filter_upwards [hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 2 hs g u,
      (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae hu] with q hq heq
    change u (g⁻¹ * q) = profile ε (t F (g⁻¹ * q)) at heq
    rw [hq, heq]
    change ((A (t F q) / A (t F (g⁻¹ * q)) : ℝ) : ℂ) *
      (A (t F (g⁻¹ * q)) * Real.exp (-ε * |t F (g⁻¹ * q)|) : ℝ) =
        (A (t F q) * Real.exp (-ε * |t F q - t F g|) : ℝ)
    rw [← Complex.ofReal_mul, ← mul_assoc, div_mul_cancel₀ _ (amplitude_pos _).ne', log_translate]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hp : (fun q : Q F => profile ε (t F q)) =ᵐ[μ] 0 :=
      hu.symm.trans (hzero ▸ Lp.coeFn_zero ℂ 2 μ)
    have hc := (profile_continuous ε).comp (ideleClassLogNorm_continuous F : Continuous (t F))
    have hz := congrFun ((hc.ae_eq_iff_eq (μ := μ) continuous_const).mp hp) 1
    exact (Complex.ofReal_ne_zero.mpr (mul_pos (amplitude_pos _) (Real.exp_pos _)).ne') hz
  · apply (mem_thetaCharacterSubspace _ _ _).mpr
    intro k
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_smul]
    have h0 : t F k.val = 0 := by
      change Real.log (ideleClassNorm F k.val) = 0
      rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
    apply Lp.ext
    filter_upwards [hTa k.val, hu] with q hq hq'
    exact hq.trans (by rw [h0, sub_zero]; exact hq'.symm)
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub u (T F μ a u), hu, hTa a] with q hsub hq hT
    rw [hsub]
    change ‖u q - T F μ a u q‖ ≤ _
    rw [hq, hT]
    change ‖((A (t F q) * Real.exp (-ε * |t F q|) : ℝ) : ℂ) -
        ((A (t F q) * Real.exp (-ε * |t F q - t F a|) : ℝ) : ℂ)‖ ≤
      (Real.exp (ε * |t F a|) - 1) * ‖((A (t F q) * Real.exp (-ε * |t F q|) : ℝ) : ℂ)‖
    rw [← Complex.ofReal_sub]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (amplitude_pos _).le (Real.exp_pos _).le), ← mul_sub, abs_mul,
      abs_of_pos (amplitude_pos _), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (exp_abs_translate_le he.le (t F a) (t F q)) (amplitude_pos _).le

/-- On the ambient trivial isotype at degree two, the actual Weil operator
has no uniform lower bound. The profile is exponential in the log norm. -/
theorem globalSobolevWeilPrincipalValue_approxInvariant (v : Place F) (B : ℝ≥0) :
    ∃ u : Lp ℂ 2 μ, u ∈ globalAmbientSobolevIsotype F (1 : PontryaginDual (K F)) μ 0 0 2 hs ∧
      (B : ℝ) * ‖globalSobolevWeilPrincipalValue F μ 2 hs v u‖ < ‖u‖ := by
  let a := globalUniformizerClass F v
  let d (ε : ℝ) := (B : ℝ) * (Real.exp (ε * |t F a|) - 1)
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hc : d 0 < 1 := by simp [d]
  have hnear : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), d ε < 1 :=
    ((hd.continuousAt.eventually (gt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hdε⟩ := (hp.and hnear).exists
  let u := (profile_memLp F μ (show 0 < ε from hε)).toLp _
  obtain ⟨hu, hω, hb⟩ := profile_difference F μ hε a
  refine ⟨u, hω, ?_⟩
  rw [globalSobolevWeilPrincipalValue_of_isotype F μ 2 hs v _ u hω]
  have hχ : (1 : PontryaginDual (K F)).comp (globalSobolevFiniteUnitInclusion F v) = 1 :=
    PontryaginDual.ext fun _ => rfl
  rw [ite_eq_left hχ]
  change (B : ℝ) * ‖u - T F μ a u‖ < ‖u‖
  calc
    _ ≤ d ε * ‖u‖ := (mul_le_mul_of_nonneg_left hb B.coe_nonneg).trans_eq (mul_assoc _ _ _).symm
    _ < ‖u‖ := mul_lt_of_lt_one_left (norm_pos_iff.mpr hu) hdε

/-- A finite nonnegative mass invariant under a translation which advances
the logarithmic coordinate by one has zero mass. -/
private theorem lintegral_eq_zero_of_logShift
    (a : Q F) (l : Q F → ℝ) (hl : Measurable l)
    (hshift : ∀ q, l (a⁻¹ * q) = l q - 1)
    {e : Q F → ℝ≥0∞} (he : (∫⁻ q, e q ∂μ) < ⊤)
    (hinv : (fun q => e (a⁻¹ * q)) =ᵐ[μ] e) : ∫⁻ q, e q ∂μ = 0 := by
  let S (n : ℤ) := l ⁻¹' Ico (n : ℝ) ((n : ℝ) + 1)
  let V (n : ℤ) := ∫⁻ q in S n, e q ∂μ
  have hS (n : ℤ) : MeasurableSet (S n) := hl measurableSet_Ico
  have hemb : MeasurableEmbedding (fun q => a⁻¹ * q) :=
    (Homeomorph.mulLeft a⁻¹).measurableEmbedding
  have hstep (n : ℤ) : V (n + 1) = V n := by
    have hpre : (fun q => a⁻¹ * q) ⁻¹' S n = S (n + 1) := by
      ext q
      change l (a⁻¹ * q) ∈ Ico (n : ℝ) ((n : ℝ) + 1) ↔
        l q ∈ Ico ((n + 1 : ℤ) : ℝ) (((n + 1 : ℤ) : ℝ) + 1)
      rw [hshift]
      push_cast
      simp only [mem_Ico]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    calc
      V (n + 1) = ∫⁻ q in S (n + 1), e (a⁻¹ * q) ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae hinv.symm)
      _ = V n := by
        rw [← hpre]
        exact (measurePreserving_mul_left μ a⁻¹).setLIntegral_comp_preimage_emb hemb e (S n)
  have hconst (n : ℤ) : V n = V 0 := by
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hstep n).trans ih
    | pred n ih =>
      have h := hstep (-(n : ℤ) - 1)
      rw [sub_add_cancel] at h
      convert h.symm.trans ih using 1
  have hcover : ⋃ n : ℤ, S n = univ := by simp only [S, ← preimage_iUnion, iUnion_Ico_intCast, preimage_univ]
  have hdisj : Pairwise (Disjoint on S) := by
    intro n m hnm
    rw [Function.onFun, Set.disjoint_left]
    intro q hqn hqm
    change l q ∈ Ico (n : ℝ) ((n : ℝ) + 1) at hqn
    change l q ∈ Ico (m : ℝ) ((m : ℝ) + 1) at hqm
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hlt' : (n : ℝ) + 1 ≤ m := by exact_mod_cast (show n + 1 ≤ m by omega)
      exact (not_lt_of_ge (hlt'.trans hqm.1)) hqn.2
    · have hgt' : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
      exact (not_lt_of_ge (hgt'.trans hqn.1)) hqm.2
  have hsum : ∫⁻ q, e q ∂μ = ∑' n : ℤ, V n := by
    rw [← setLIntegral_univ, ← hcover, lintegral_iUnion hS hdisj]
  simp_rw [hconst] at hsum
  by_cases h : V 0 = 0
  · simpa only [h, tsum_zero] using hsum
  · exact (he.ne (hsum.trans (ENNReal.tsum_const_eq_top_of_ne_zero h))).elim

/-- Translation by a nonzero logarithmic norm has no fixed vector in the
weighted degree-two Haar space. -/
theorem globalSobolevTranslation_degreeTwo_fixed_eq_zero (a : Q F) (ha : t F a ≠ 0)
    (u : Lp ℂ 2 μ) (h : T F μ a u = u) : u = 0 := by
  let l (q : Q F) := t F q / t F a
  let w (q : Q F) : ℂ := u q / (A (t F q) : ℂ)
  let e (q : Q F) := ENNReal.ofReal (‖w q‖ ^ 2)
  have hc : Continuous (t F) := ideleClassLogNorm_continuous F
  have hlam : Continuous (fun q : Q F => A (t F q)) := by simp_rw [amplitude_formula]; fun_prop
  have hrecip : Continuous (fun q : Q F => ((A (t F q) : ℝ) : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hlam).inv₀ fun q =>
      Complex.ofReal_ne_zero.mpr (amplitude_pos _).ne'
  have hw : AEStronglyMeasurable w μ := by
    apply ((Lp.aestronglyMeasurable u).mul hrecip.aestronglyMeasurable).congr
    exact .of_forall fun q => (div_eq_mul_inv (u q) (A (t F q) : ℂ)).symm
  have hm : AEMeasurable e μ := (hw.norm.pow 2).aemeasurable.ennreal_ofReal
  have hnorm (q : Q F) : ‖w q‖ ≤ ‖u q‖ := by
    have hab : 1 ≤ A (t F q) := by
      rw [amplitude_formula]
      exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg (t F q)])
    unfold w
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (amplitude_pos _).le]
    exact div_le_self (norm_nonneg _) hab
  have hi : Integrable (fun q => ‖u q‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hfin : (∫⁻ q, e q ∂μ) < ⊤ :=
    (lintegral_mono fun q => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hnorm q) 2)).trans_lt
      ((hasFiniteIntegral_iff_ofReal (.of_forall fun q => sq_nonneg ‖u q‖)).mp hi.2)
  have heinv : (fun q => w (a⁻¹ * q)) =ᵐ[μ] w := by
    have hT := hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 2 hs a u
    rw [h] at hT
    filter_upwards [hT] with q hq
    have hA : (A (t F q) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (amplitude_pos _).ne'
    have hB : (A (t F (a⁻¹ * q)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (amplitude_pos _).ne'
    change u q = ((A (t F q) / A (t F (a⁻¹ * q)) : ℝ) : ℂ) * u (a⁻¹ * q) at hq
    change u (a⁻¹ * q) / (A (t F (a⁻¹ * q)) : ℂ) = u q / (A (t F q) : ℂ)
    rw [hq, Complex.ofReal_div]
    field_simp
  have hshift (q : Q F) : l (a⁻¹ * q) = l q - 1 := by
    dsimp only [l]
    rw [log_translate, sub_div, div_self ha]
  have hz := lintegral_eq_zero_of_logShift F μ a l (hc.measurable.div_const _) hshift hfin
    (heinv.mono fun q hq => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hq)
  have hae := (lintegral_eq_zero_iff' hm).mp hz
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℂ 2 μ] with q hq hq₀
  rw [hq₀]
  change ENNReal.ofReal (‖w q‖ ^ 2) = 0 at hq
  have hqw : w q = 0 := norm_eq_zero.mp (by nlinarith [ENNReal.ofReal_eq_zero.mp hq])
  exact (div_eq_zero_iff.mp hqw).resolve_right
    (Complex.ofReal_ne_zero.mpr (amplitude_pos _).ne')

private theorem uniformizer_log_ne_zero (v : Place F) : t F (globalUniformizerClass F v) ≠ 0 := by
  change Real.log (ideleClassNorm F (ideleClassMap F
    (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) ≠ 0
  rw [ideleClassNorm_mk, singleFiniteIdele_norm,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv, neg_ne_zero]
  exact (Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'

/-- The ambient degree-two Weil operator of a single place is injective.
A vector in its kernel is fixed by the unit average and by the uniformizer. -/
theorem globalSobolevWeilPrincipalValue_degreeTwo_injective (v : Place F) :
    Injective (globalSobolevWeilPrincipalValue F μ 2 hs v) := by
  let P := globalSobolevFiniteUnitAverage F μ 2 hs v
  let g := globalUniformizerClass F v
  let U := globalSobolevWeilPrincipalValue F μ 2 hs v
  apply U.toLinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  change x - T F μ g (P x) = 0 at hx
  have he : x = T F μ g (P x) := sub_eq_zero.mp hx
  have hc := DFunLike.congr_fun (globalSobolevFiniteUnitAverage_commute_translate F μ 2 hs v g).eq (P x)
  change P (T F μ g (P x)) = T F μ g (P (P x)) at hc
  have hid : P (P x) = P x := globalSobolevFiniteUnitAverage_idempotent F μ 2 hs v x
  have hPx : P x = x := calc
    P x = P (T F μ g (P x)) := congrArg P he
    _ = T F μ g (P (P x)) := hc
    _ = x := by rw [hid]; exact he.symm
  have hfix : T F μ g x = x := by simpa only [hPx] using he.symm
  exact globalSobolevTranslation_degreeTwo_fixed_eq_zero F μ g (uniformizer_log_ne_zero F v) x hfix

/-- A single Weil factor has nonclosed range on the ambient degree-two
weighted Haar space, in every number field. -/
theorem globalSobolevWeilPrincipalValue_degreeTwo_nonclosed (v : Place F) :
    ¬ IsClosed (range (globalSobolevWeilPrincipalValue F μ 2 hs v)) := by
  let D := globalSobolevWeilPrincipalValue F μ 2 hs v
  intro hclosed
  obtain ⟨B, hB⟩ := D.antilipschitz_of_injective_of_isClosed_range
    (globalSobolevWeilPrincipalValue_degreeTwo_injective F μ v) hclosed
  obtain ⟨u, _, hu⟩ := globalSobolevWeilPrincipalValue_approxInvariant F μ v B
  have h := hB.le_mul_dist u 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  exact hu.not_ge h

/-- For the intrinsic theta completion the same singleton refutation needs
only the trivial norm-one isotype to lie in that completion. -/
theorem globalThetaSobolevWeilPrincipalValues_singleton_nonclosed_of_contains_trivial
    (v : Place F)
    (hdense : globalAmbientSobolevIsotype F (1 : PontryaginDual (K F)) μ 0 0 2 hs ≤
      globalThetaSobolevCompletion F μ 0 0 0 2 hs) :
    ¬ IsClosed (range (globalThetaSobolevWeilPrincipalValues F μ 2 hs {v})) := by
  let N := globalThetaSobolevCompletion F μ 0 0 0 2 hs
  let E := globalThetaSobolevWeilPrincipalValue F μ 2 hs v
  letI : CompleteSpace N := (globalThetaSobolevCompletion_isClosed F μ 0 0 0 2 hs).completeSpace_coe
  have hsingleton : globalThetaSobolevWeilPrincipalValues F μ 2 hs {v} = E :=
    Finset.noncommProd_singleton _ _
  rw [hsingleton]
  intro hclosed
  have hE : Injective E := by
    intro x y hxy
    apply Subtype.ext
    exact globalSobolevWeilPrincipalValue_degreeTwo_injective F μ v (congrArg Subtype.val hxy)
  obtain ⟨B, hB⟩ := E.antilipschitz_of_injective_of_isClosed_range hE hclosed
  obtain ⟨u, hu, hsmall⟩ := globalSobolevWeilPrincipalValue_approxInvariant F μ v B
  let x : N := ⟨u, hdense hu⟩
  have h := hB.le_mul_dist x 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  exact hsmall.not_ge h

end
end Masullo
