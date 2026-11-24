import BruhatSplitSchwartz
import CompactElementaryFourierDecay
import ModulationSection
import CompactGroupMellin
import ModulatedDecayAngularCoefficients

open Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]

include hτ in
/-- Angular Fourier integration of ordinary Schwartz–Bruhat tests, with
values in the real Schwartz topology. -/
def bruhatAngularFourier (χ : PontryaginDual K) : BruhatSchwartz G →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.postcompCLM (compactCharacterIntegral ν (⟨fun k => (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩ : C(K, ℂ))
    (fun k => Circle.norm_coe (χ k)))).comp (exists_bruhatSplitSchwartz m τ hτ).choose

include hτ in
theorem bruhatAngularFourier_apply (χ : PontryaginDual K) (f : BruhatSchwartz G) (x : ℝ) :
    bruhatAngularFourier m τ hτ ν χ f x =
      ∫ k : K, f.val (τ (Multiplicative.ofAdd x) * k.val) * (χ k : ℂ) ∂ν := by
  change (∫ k : K, (exists_bruhatSplitSchwartz m τ hτ).choose f x k * (χ k : ℂ) ∂ν) = _
  exact integral_congr_ae (.of_forall fun k =>
    congrArg (fun z : ℂ => z * (χ k : ℂ)) ((exists_bruhatSplitSchwartz m τ hτ).choose_spec f x k))

private theorem schwartz_postcomp_seminorm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : V →L[ℂ] ℂ) (f : 𝓢(ℝ, V)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.postcompCLM L f) ≤
      ‖L‖ * SchwartzMap.seminorm ℂ k n f := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have hd := (L.restrictScalars ℝ).norm_iteratedFDeriv_comp_left
    (n := n) (x := x) (f.smooth' : ContDiff ℝ ∞ (f : ℝ → V)).contDiffAt
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (L ∘ f) x‖ ≤ _
  calc
    _ ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f x‖) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k n f x) (norm_nonneg _)

include hτ in
/-- A single continuous Schwartz seminorm bounds every angular coefficient. -/
theorem bruhatAngularFourier_seminorm_uniform (k n : ℕ) :
    ∃ P : Seminorm ℂ (BruhatSchwartz G), Continuous P ∧
      ∀ χ : PontryaginDual K, ∀ f : BruhatSchwartz G,
        SchwartzMap.seminorm ℂ k n (bruhatAngularFourier m τ hτ ν χ f) ≤ ν.real univ * P f := by
  let S := (exists_bruhatSplitSchwartz m τ hτ).choose
  let P := (SchwartzMap.seminorm ℂ k n : Seminorm ℂ 𝓢(ℝ, C(K, ℂ))).comp S.toLinearMap
  refine ⟨P, ((schwartz_withSeminorms ℂ ℝ C(K, ℂ)).continuous_seminorm (k,n)).comp S.continuous, fun χ f => ?_⟩
  let L := compactCharacterIntegral ν (⟨fun k => (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩ : C(K, ℂ)) (fun k => Circle.norm_coe (χ k))
  have hL : ‖L‖ ≤ ν.real univ := by
    refine L.opNorm_le_bound (by positivity) fun g => ?_
    change ‖∫ x : K, g x * (χ x : ℂ) ∂ν‖ ≤ _
    rw [mul_comm]
    apply norm_integral_le_of_norm_le_const
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact g.norm_coe_le_norm x
  exact (schwartz_postcomp_seminorm_le L (S f) k n).trans
    (mul_le_mul_of_nonneg_right hL (apply_nonneg _ _))

include hτ in
set_option maxHeartbeats 2500000 in
/-- Differentiation in a norm-one direction acts on the entire radial
Schwartz coefficient by multiplication by the character frequency. -/
theorem bruhatAngularFourier_derivative (c : Multiplicative ℝ →ₜ* K)
    (χ : PontryaginDual K) (u : ℝ)
    (hχ : ∀ t : ℝ, (χ (c (Multiplicative.ofAdd t)) : ℂ) =
      Complex.exp ((u * t : ℝ) * Complex.I)) (f : BruhatSchwartz G) :
    bruhatAngularFourier m τ hτ ν χ
        (bruhatSchwartz_derivative ((modulatedKernelInclusion m).comp c) f) =
      (-(u : ℂ) * Complex.I) • bruhatAngularFourier m τ hτ ν χ f := by
  let d := (modulatedKernelInclusion m).comp c
  let D := bruhatSchwartz_derivative d f
  apply SchwartzMap.ext
  intro x
  let j (k : K) := τ (Multiplicative.ofAdd x) * k.val
  have hj : Continuous j := continuous_const.mul continuous_subtype_val
  have hd (k : K) : HasDerivAt (fun t : ℝ => f.val (j (c (Multiplicative.ofAdd t) * k)))
      (D.val (j k)) 0 := by
    have h := (bruhatOrbitDeriv_regular d f.val (s := 0)
      (bruhatSchwartz_le_smooth f.property 1)).2 (j k)
    change HasDerivAt (fun t : ℝ => f.val (j k * d (Multiplicative.ofAdd t))) (D.val (j k)) 0 at h
    have he : (fun t : ℝ => j k * d (Multiplicative.ofAdd t)) =
        fun t => j (c (Multiplicative.ofAdd t) * k) := by
      funext t
      change (τ (Multiplicative.ofAdd x) * k.val) * (c (Multiplicative.ofAdd t)).val =
        τ (Multiplicative.ofAdd x) * ((c (Multiplicative.ofAdd t)).val * k.val)
      rw [mul_assoc, mul_comm k.val]
    have hfun : (fun t : ℝ => f.val (j k * d (Multiplicative.ofAdd t))) =
        fun t => f.val (j (c (Multiplicative.ofAdd t) * k)) :=
      funext fun t => congrArg f.val (congrFun he t)
    exact hfun ▸ h
  change bruhatAngularFourier m τ hτ ν χ D x =
    (-(u : ℂ) * Complex.I) * bruhatAngularFourier m τ hτ ν χ f x
  rw [bruhatAngularFourier_apply, bruhatAngularFourier_apply]
  exact integral_character_orbitDerivative ν c χ u (f.val ∘ j) (D.val ∘ j)
    ((bruhatSchwartz_continuous f).comp hj) ((bruhatSchwartz_continuous D).comp hj) hd hχ

include hτ in
set_option maxHeartbeats 2500000 in
/-- A real weight can be applied before taking the angular Fourier coefficient.
The equality is in the real Schwartz space. -/
theorem logTwist_angularCoefficient (hm : IsProperMap m) (I : Set ℝ) (b : I)
    (χ : PontryaginDual K) (f : ModulatedExponentialInductive m I) :
    logExponentialDecayTwist I b
      (modulatedDecayAngularCoefficient m τ hτ ν χ I ⟨b,b.property⟩ hm f) =
    bruhatAngularFourier m τ hτ ν χ (modulatedDecayTwistCLM m I b f) := by
  apply SchwartzMap.ext
  intro x
  let c := modulatedDecayAngularCoefficient m τ hτ ν χ I ⟨b,b.property⟩ hm f
  let J (u : K) := f.val (τ (Multiplicative.ofAdd x) * u.val) * (χ u : ℂ)
  let w : ℂ := Real.exp ((b : ℝ) * x)
  have h1 : logExponentialDecayTwist I b c x = w * ∫ u, J u ∂ν :=
    (logExponentialDecayTwist_apply I b c x).trans
      (congrArg (w * ·) (modulatedDecayAngularCoefficient_apply m τ hτ ν χ I
        ⟨b,b.property⟩ hm f x))
  change logExponentialDecayTwist I b c x = _
  rw [h1, ← integral_const_mul, bruhatAngularFourier_apply]
  refine integral_congr_ae (.of_forall fun u => ?_)
  let g := τ (Multiplicative.ofAdd x) * u.val
  have hg : (m g).toAdd = x := by
    change (m (τ (Multiplicative.ofAdd x) * u.val)).toAdd = x
    rw [map_mul, hτ, show m u.val = 1 from u.property, mul_one]
    rfl
  change w * (f.val g * (χ u : ℂ)) = modulatedExponentialWeight m b f.val g * (χ u : ℂ)
  rw [modulatedExponentialWeight_apply, hg, Complex.real_smul]
  exact (mul_assoc _ _ _).symm

include hτ in
/-- Repeated integration by parts acts by the corresponding power of the
frequency in every radial Schwartz seminorm. -/
theorem bruhatAngularFourier_iterate (c : Multiplicative ℝ →ₜ* K)
    (χ : PontryaginDual K) (u : ℝ)
    (hχ : ∀ t : ℝ, (χ (c (Multiplicative.ofAdd t)) : ℂ) =
      Complex.exp ((u * t : ℝ) * Complex.I)) (f : BruhatSchwartz G) (d : ℕ) :
    bruhatAngularFourier m τ hτ ν χ
        ((bruhatSchwartz_derivative ((modulatedKernelInclusion m).comp c))^[d] f) =
      (-(u : ℂ) * Complex.I) ^ d • bruhatAngularFourier m τ hτ ν χ f := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', bruhatAngularFourier_derivative m τ hτ ν c χ u hχ,
      ih, smul_smul, pow_succ']

include hτ in
set_option maxHeartbeats 2500000 in
/-- Finite families of angular directions give simultaneous polynomial decay
in their frequencies in any prescribed radial Schwartz seminorm. -/
theorem bruhatAngularFourier_polynomialBound {t : ℕ} {Ω : Type*} (character : Ω → PontryaginDual K)
    (c : Fin t → (Multiplicative ℝ →ₜ* K)) (u : Ω → Fin t → ℝ)
    (hχ : ∀ (χ : Ω) (j : Fin t) (s : ℝ),
      (character χ (c j (Multiplicative.ofAdd s)) : ℂ) = Complex.exp ((u χ j * s : ℝ) * Complex.I))
    (f : BruhatSchwartz G) (k n d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : Ω,
      (1 + ∑ j, ‖u χ j‖) ^ (d+1) *
        SchwartzMap.seminorm ℂ k n (bruhatAngularFourier m τ hτ ν (character χ) f) ≤ C := by
  obtain ⟨P, _, hP⟩ := bruhatAngularFourier_seminorm_uniform m τ hτ ν k n
  let D (j : Fin t) := bruhatSchwartz_derivative ((modulatedKernelInclusion m).comp (c j))
  let C := ((t : ℝ) + 1) ^ d * (ν.real univ * P f +
    ∑ j, ν.real univ * P ((D j)^[d+1] f))
  refine ⟨C, by dsimp [C]; positivity, fun χ => ?_⟩
  let a (j : Fin t) := ‖u χ j‖
  let w : Fin (t+1) → ℝ := Fin.cons 1 a
  let Q := SchwartzMap.seminorm ℂ k n (bruhatAngularFourier m τ hτ ν (character χ) f)
  have hpow : (1 + ∑ j, a j) ^ (d+1) ≤
      ((t : ℝ) + 1) ^ d * (1 + ∑ j, a j ^ (d+1)) := by
    have hw (j : Fin (t+1)) : 0 ≤ w j := by
      refine Fin.cases ?_ (fun l => ?_) j
      · simp [w]
      · exact norm_nonneg _
    simpa [w, Fin.sum_univ_succ, Fin.cons_succ] using
      (pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := w) (fun j _ => hw j) d)
  have ha (j : Fin t) : a j ^ (d+1) * Q ≤ ν.real univ * P ((D j)^[d+1] f) := by
    have he := bruhatAngularFourier_iterate m τ hτ ν (c j) (character χ) (u χ j) (hχ χ j) f (d+1)
    have hb := congrArg (SchwartzMap.seminorm ℂ k n) he
    rw [map_smul_eq_mul, norm_pow, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one] at hb
    exact (le_of_eq hb.symm).trans (hP (character χ) ((D j)^[d+1] f))
  calc
    _ ≤ (((t : ℝ) + 1)^d * (1 + ∑ j, a j^(d+1))) * Q :=
      mul_le_mul_of_nonneg_right hpow (apply_nonneg _ _)
    _ = ((t : ℝ) + 1)^d * (Q + ∑ j, a j^(d+1) * Q) := by
      rw [mul_assoc, add_mul, one_mul, Finset.sum_mul]
    _ ≤ C := mul_le_mul_of_nonneg_left
      (add_le_add (hP (character χ) f) (Finset.sum_le_sum fun j _ => ha j)) (by positivity)

variable {n : ℕ} {T : Type*} [AddCommGroup T] [TopologicalSpace T]
  [DiscreteTopology T] [Finite T]

include hτ in
set_option maxHeartbeats 4300000 in
/-- Along an elementary quotient of the compact kernel, every weighted
radial Schwartz seminorm of the Fourier coefficients decays rapidly in
the actual lattice frequency. -/
theorem splitAngularCoefficient_rapid_decay [LocallyCompactSpace K]
    (φ : K →ₜ* Multiplicative (ElementaryLCAModel 0 n 0 T)) (hφ : Surjective φ)
    (hm : IsProperMap m) (I : Set ℝ) (b : I) (f : ModulatedExponentialInductive m I)
    (k r d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : PontryaginDual (Multiplicative (ElementaryLCAModel 0 n 0 T)),
      compactElementaryFrequencyWeight θ ^ (d+1) * SchwartzMap.seminorm ℂ k r
        (logExponentialDecayTwist I b (modulatedDecayAngularCoefficient m τ hτ ν
          (θ.comp φ) I ⟨b,b.property⟩ hm f)) ≤ C := by
  classical
  let A := ElementaryLCAModel 0 n 0 T
  let Ω := PontryaginDual (Multiplicative A)
  letI : T2Space T := DiscreteTopology.toT2Space
  letI : T2Space (Multiplicative A) := inferInstanceAs (T2Space A)
  let a (j : Fin n) : Multiplicative ℝ →ₜ* Multiplicative A :=
    elementaryOneParameter (elementaryTorusVelocity j)
  choose c hc using fun j => exists_oneParameter_lift_proper φ φ.continuous.isProperMap hφ (a j)
  let character (θ : Ω) : PontryaginDual K := θ.comp φ
  let u (θ : Ω) (j : Fin n) := 2 * Real.pi * (compactElementaryCharacter_frequency θ j : ℝ)
  have hphase (θ : Ω) (j : Fin n) (s : ℝ) :
      (character θ (c j (Multiplicative.ofAdd s)) : ℂ) = Complex.exp ((u θ j * s : ℝ) * Complex.I) := by
    have he : φ (c j (Multiplicative.ofAdd s)) = a j (Multiplicative.ofAdd s) :=
      DFunLike.congr_fun (hc j) _
    change (θ (φ (c j (Multiplicative.ofAdd s))) : ℂ) = _
    rw [he]
    change (θ (Multiplicative.ofAdd (elementaryCoverHom (s • elementaryTorusVelocity j))) : ℂ) = _
    rw [compactElementaryCharacterPhase_spec, Circle.coe_exp, map_smul, smul_eq_mul,
      compactElementaryCharacter_frequency_spec, mul_comm s]
  obtain ⟨C, hC, hbound⟩ := bruhatAngularFourier_polynomialBound m τ hτ ν character c u hphase
    (modulatedDecayTwistCLM m I b f) k r d
  refine ⟨C, hC, fun θ => ?_⟩
  have hw : compactElementaryFrequencyWeight θ ≤ 1 + ∑ j, ‖u θ j‖ := by
    unfold compactElementaryFrequencyWeight
    apply add_le_add (le_refl (1 : ℝ))
    apply Finset.sum_le_sum
    intro j _
    change ‖(compactElementaryCharacter_frequency θ j : ℝ)‖ ≤
      ‖(2 * Real.pi) * (compactElementaryCharacter_frequency θ j : ℝ)‖
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hnonneg : 0 ≤ compactElementaryFrequencyWeight θ :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have he := logTwist_angularCoefficient m τ hτ ν hm I b (θ.comp φ) f
  rw [he]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnonneg hw (d+1)) (apply_nonneg _ _)).trans
    (hbound θ)

end

end Masullo
