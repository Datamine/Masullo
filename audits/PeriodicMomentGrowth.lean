module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6_Printed
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a

/-! The growth estimate for Theorem 4.6.1.5. The Mellin chart construction
adapts `modulatedQuotientLogMoment_bases_quotient` from the Apache-2.0
RiemannMasullo project. Build in the archived original revision
`3897f9497d5cff426d6548150bb3c67bc96d87eb` on Lean 4.36.0. -/

open Function MeasureTheory Set Topology TopologicalSpace
open scoped NNReal

namespace RiemannMasullo

noncomputable section

private theorem periodicTranslate_seminorm_bound
    {A : Type*} [Fintype A] (F : A → SchwartzBergman univ)
    (q : Seminorm ℂ (SchwartzBergman univ)) (hq : Continuous q) :
    ∃ d : ℕ, ∃ C > (0 : ℝ), ∀ a t, q (moment_translate (F a) t) ≤ C * (1 + |t|) ^ d := by
  classical
  let lines := LinearMap.pi (bergmanLine isOpen_univ ordConnected_univ)
  let family := (SeminormFamily.sigma fun a : (univ : Set ℝ) ↦
    (schwartzSeminormFamily ℂ ℝ ℂ).comp (LinearMap.proj a)).comp lines
  have htop : (inferInstance : TopologicalSpace (SchwartzBergman univ)) =
      induced lines inferInstance := (bergman_embedding isOpen_univ ordConnected_univ).eq_induced
  have hs : WithSeminorms family := (congrArg (fun t ↦ WithSeminorms (topology := t) family) htop).mpr
    (lines.withSeminorms_induced (withSeminorms_pi fun _ : (univ : Set ℝ) ↦
      schwartz_withSeminorms ℂ ℝ ℂ))
  obtain ⟨s, c, hc, hsBound⟩ := Seminorm.bound_of_continuous hs q hq
  let weight (i : (a : (univ : Set ℝ)) × (ℕ × ℕ)) := i.2.1
  let d := s.sup weight
  have hBound (a : A) (i : (a : (univ : Set ℝ)) × (ℕ × ℕ)) :
      ∃ C ≥ (0 : ℝ), ∀ t, family i (moment_translate (F a) t) ≤ (1 + |t|) ^ weight i * C := by
    rcases i with ⟨x, p, k⟩
    exact moment_translate_bound (F a) x p k
  choose C hC hEst using hBound
  let M := 1 + ∑ a : A, ∑ i ∈ s, C a i
  have hM : 0 < M := by
    dsimp [M]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun a _ ↦
      Finset.sum_nonneg fun i _ ↦ hC a i)
  have hc' : 0 < (c : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  refine ⟨d, (c : ℝ) * M, mul_pos hc' hM, fun a t ↦ ?_⟩
  refine (hsBound (moment_translate (F a) t)).trans ?_
  change (c : ℝ) * s.sup family (moment_translate (F a) t) ≤ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc'.le
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro i hi
  have hCi : C a i ≤ M := by
    have h₁ : C a i ≤ ∑ j ∈ s, C a j :=
      Finset.single_le_sum (fun j _ ↦ hC a j) hi
    have h₂ : (∑ j ∈ s, C a j) ≤ ∑ a : A, ∑ j ∈ s, C a j :=
      Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg fun j _ ↦ hC a j) (Finset.mem_univ a)
    exact (h₁.trans h₂).trans (le_add_of_nonneg_left zero_le_one)
  exact (hEst a i t).trans (by
    rw [mul_comm M]
    exact mul_le_mul (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Finset.le_sup hi)) hCi
      (hC a i) (by positivity))

private theorem periodicMoment_lattice_growth {X ι A : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [Finite A]
    (e : (A × ℤ) ≃ ι) (s : ι → ℝ) (b : A → ℝ) (r : A → ℕ) {T : ℝ} (hT : 0 < T)
    (hb : ∀ a, b a ∈ Ico 0 T) (hes : ∀ a (n : ℤ), s (e (a,n)) = b a + n*T)
    (Q : SchwartzBergman univ →L[ℂ] X) (hsur : Surjective Q) (c : ℂ)
    (d : ι → StrongDual ℂ X) (ψ : ι → X)
    (he : ∀ H a (n : ℤ), d (e (a,n)) (Q H) =
      c * iteratedDeriv (r a) H.val (((b a + n*T : ℝ) : ℂ)*Complex.I))
    (hsep : ∀ u, (∀ j, d j u = 0) → u = 0)
    (hbi : (∀ j, d j (ψ j) = 1) ∧ ∀ j k, j ≠ k → d j (ψ k) = 0)
    (q : Seminorm ℂ X) (hq : Continuous q) :
    ∃ p : ℕ, ∃ C > (0 : ℝ), ∀ j, q (ψ j) ≤ C * (1 + |s j|) ^ p := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hdelta (i j : ι) : d i (ψ j) = if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst j
      simp [hbi.1]
    · simp [h, hbi.2 _ _ h]
  choose F hF using fun a : A ↦ hsur (ψ (e (a,0)))
  have htr (a : A) (n : ℤ) : Q (moment_translate (F a) (n*T)) = ψ (e (a,n)) := by
    apply sub_eq_zero.mp
    apply hsep
    intro j
    obtain ⟨⟨a',k⟩,rfl⟩ := e.surjective j
    rw [map_sub, sub_eq_zero, he]
    change c * iteratedDeriv (r a') (fun z : ℂ ↦ (F a).val (z - ((n*T : ℝ) : ℂ)*Complex.I)) _ = _
    rw [iteratedDeriv_comp_sub_const]
    have harg : ((b a' + k*T : ℝ) : ℂ)*Complex.I - ((n*T : ℝ) : ℂ)*Complex.I =
        ((b a' + (k-n : ℤ)*T : ℝ) : ℂ)*Complex.I := by push_cast; ring
    dsimp only
    rw [harg, ← he, hF, hdelta, hdelta]
    simp only [e.injective.eq_iff, Prod.mk.injEq, sub_eq_zero]
  obtain ⟨p, C, hC, hqC⟩ := periodicTranslate_seminorm_bound F
    (q.comp Q.toLinearMap) (hq.comp Q.continuous)
  refine ⟨p, C * (1 + T) ^ p, by positivity, fun j ↦ ?_⟩
  obtain ⟨⟨a,n⟩,rfl⟩ := e.surjective j
  rw [← htr]
  have hcenter : |(n : ℝ) * T| ≤ |s (e (a,n))| + T := by
    rw [hes]
    have ht := abs_sub (s (e (a,n))) (b a)
    rw [hes, add_sub_cancel_left, abs_of_nonneg (hb a).1] at ht
    exact ht.trans (add_le_add_right (hb a).2.le _)
  have hweight : 1 + |(n : ℝ) * T| ≤ (1 + T) * (1 + |s (e (a,n))|) := by
    nlinarith [mul_nonneg hT.le (abs_nonneg (s (e (a,n))))]
  exact (hqC a ((n : ℝ)*T)).trans (by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hweight p) hC.le)

section Modulated

set_option quotPrecheck false

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
  (ω : PontryaginDual m.toMonoidHom.ker) {N : ℕ} (γs : Fin N → G)
  (hγs : ∀ k, 1 < (m (γs k)).val)
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
  (t₀ : Fin N → PontryaginDual m.toMonoidHom.ker → ℝ)
  (ht₀ : ∀ k ω',
    let L := Real.log ((m (γs k)).val : ℝ)
    t₀ k ω' ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ k ω' * L) = χ ω' (γs k))
  (hcomm : ∃ a : ℝ, 0 < a ∧ ∀ k, ∃ r : ℚ, Real.log ((m (γs k)).val : ℝ) = (r : ℝ) * a)

local notation "K" => m.toMonoidHom.ker
local notation "period" x => Real.log ((m x).val : ℝ)
local notation "S" => List.ofFn γs
local notation "R" => (modulatedIsotypicDifferenceProduct m hm hms ω
  univ ordConnected_univ (mem_univ _) S).range
local notation "U" => (modulatedDecayIsotype m univ (mem_univ 0) ω ⧸ R)
local notation "J" => {p : PontryaginDual G × ℕ // p.2 < modulatedPeriodicMultiplicity m ω γs p.1}
local notation "D" => (modulatedQuotientLogMoment (m := m) (hm := hm) (hms := hms)
  (ω := ω) (γs := γs) (hγs := hγs) (μ := μ))
local notation "freq[" k "," n "]" =>
  ((PontryaginDual.map
    (⟨QuotientGroup.mk' (Subgroup.zpowers (γs k)), QuotientGroup.continuous_mk⟩ :
      G →ₜ* (G ⧸ Subgroup.zpowers (γs k)))
    (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω, n)))⁻¹)

include hcomm in
/-- The biorthogonal vectors grow at most polynomially on every cyclic lattice
when the logarithmic periods are commensurate. -/
public theorem modulatedQuotientLogMoment_growth_corrected
    (ψ : J → U) (hbi : (∀ j, D j (ψ j) = 1) ∧ ∀ j k, j ≠ k → D j (ψ k) = 0)
    (q : Seminorm ℂ U) (hq : Continuous q) :
    ∃ d : ℕ, ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : J), j.val.1 = freq[k, n] →
        q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  obtain ⟨τ, hτ⟩ := exists_surjectiveModulation_section m hm hms
  obtain ⟨χ₀, s, hK, h₀, hξ⟩ := moment_chart m ω γs τ hτ
  obtain ⟨p, hp⟩ := moment_profile_equiv m hm hms ω τ hτ χ₀ hK h₀ (isotype_frechet m hm hms ω)
  let M := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let e := p.trans M
  let Q := (R).mkQL.comp e.symm.toContinuousLinearMap
  have hsur : Surjective Q := (R).mkQ_surjective.comp e.symm.surjective
  obtain ⟨c, hc, hμ⟩ := moment_haar_scale m hm hms μ
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hjet (H : SchwartzBergman univ) (j : J) : D j (Q H) =
      ((c : ℝ) : ℂ) * iteratedDeriv j.val.2 H.val ((s j : ℂ) * Complex.I) := by
    change D j ((R).mkQ (e.symm H)) = _
    rw [modulatedQuotientLogMoment_mkQ, moment_profile_pairing m ω μ χ₀ _ _ (hξ j) _ _
      (hp (e.symm H)) c hμ]
    congr 2
    funext z
    exact (positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty _ z
      (mem_univ _)).symm.trans (congrArg (fun H : SchwartzBergman univ ↦ H.val z) (e.apply_symm_apply H))
  let L (k : Fin N) := -(period (γs k))
  let a (k : Fin N) := (χ₀ (γs k))⁻¹
  let factor (k : Fin N) (z : ℂ) := (a k : ℂ) * Complex.exp ((L k : ℂ) * z)
  let P (z : ℂ) := ∏ k, (1 - factor k z)
  let d (z : ℂ) := (Finset.univ.filter (fun k ↦ factor k z = 1)).card
  have hL (k : Fin N) : L k < 0 := neg_lt_zero.mpr (Real.log_pos (by exact_mod_cast hγs k))
  obtain ⟨hP, _, ho⟩ := moment_exponential_product L hL a
  change Differentiable ℂ P at hP
  change ∀ z, analyticOrderAt P z = d z at ho
  have hnz : ∃ z, P z ≠ 0 := by
    by_contra! h
    have htop : analyticOrderAt P 0 = ⊤ := analyticOrderAt_eq_top.mpr (.of_forall h)
    rw [ho] at htop
    exact ENat.natCast_ne_top _ htop
  obtain ⟨T,hT,hperiod⟩ := moment_common_period L (by
    obtain ⟨t,ht,ht'⟩ := hcomm
    refine ⟨t,ht,fun k ↦ ?_⟩
    obtain ⟨q,hq⟩ := ht' k
    exact ⟨-q, by simp only [L,hq,Rat.cast_neg,neg_mul]⟩)
  have hf (k : Fin N) : Function.Periodic (factor k) ((T : ℂ)*Complex.I) := by
    intro z
    simp only [factor, mul_add, Complex.exp_add, hperiod, mul_one]
  have hper : Function.Periodic P ((T : ℂ)*Complex.I) := fun z ↦ by simp only [P,hf _ z]
  have hdper : Function.Periodic d ((T : ℂ)*Complex.I) := fun z ↦ by simp only [d,hf _ z]
  obtain ⟨hinj,hj,hcover⟩ := moment_chart_coverage m ω γs hγs τ hτ χ₀ hK h₀ s hξ
  change ∀ j : J, j.val.2 < d ((s j : ℂ)*Complex.I) at hj
  change ∀ z k, k < d z → ∃ j : J, z = (s j : ℂ)*Complex.I ∧ k = j.val.2 at hcover
  have hsep (u : U) (hu : ∀ j, D j u = 0) : u = 0 := by
    obtain ⟨H,rfl⟩ := hsur u
    obtain ⟨F,hF⟩ := moment_periodic_division hP hnz hT hper H d ho (by
      intro z k hk
      obtain ⟨j, rfl, rfl⟩ := hcover z k hk
      exact (mul_eq_zero.mp ((hjet H j).symm.trans (hu j))).resolve_left hc')
    change (R).mkQ (e.symm H) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨e.symm F, e.injective ?_⟩
    rw [e.apply_symm_apply]
    apply Subtype.ext
    funext z
    have he := moment_product_action m hm hms ω τ hτ χ₀ h₀ p hp S (e.symm F) z
    rw [List.map_ofFn, List.prod_ofFn] at he
    exact he.trans ((congrArg (P z * ·) (congrArg (fun H : SchwartzBergman univ ↦ H.val z)
      (e.apply_symm_apply F))).trans (hF z))
  obtain ⟨hfin, enum, henum⟩ := moment_period_orbits s (fun j : J ↦ j.val.2) hinj hT d hdper
    hj hcover hP hnz ho (N := N) (fun z ↦ (Finset.card_filter_le _ _).trans (by simp))
  let A := {j : J // s j ∈ Ico 0 T}
  let : Finite A := hfin
  obtain ⟨p, C, hC, hqC⟩ := periodicMoment_lattice_growth enum s
    (fun a : A ↦ s a.val) (fun a : A ↦ a.val.val.2) hT (fun a ↦ a.property)
    (fun a n ↦ (henum a n).1) Q hsur (c : ℝ) D ψ
    (fun H a n ↦ by rw [hjet, (henum a n).1, (henum a n).2]) hsep hbi q hq
  obtain ⟨β, hβ⟩ := exists_circleExp_freq ((χ ω).comp τ)
  refine ⟨p, fun k ↦ ?_⟩
  let L := period (γs k)
  let a := 2 * Real.pi / L
  let A₀ := 1 + |β - t₀ k ω| + |a|
  refine ⟨C * A₀ ^ p, by positivity, fun n j hj ↦ ?_⟩
  have hfreq (x : G) :
      freq[k, n] x = χ ω x * Circle.exp (-(t₀ k ω - a * (n : ℝ)) * period x) := by
    change (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω, n)
      (QuotientGroup.mk x))⁻¹ = _
    have hphase : -(t₀ k ω - a * (n : ℝ)) * (period x) =
        -((t₀ k ω - 2 * Real.pi * (n : ℝ) / L) * (period x)) := by
      dsimp [a]
      ring
    rw [modulatedCyclicCharacter_mk, hphase, Circle.exp_neg, mul_inv, inv_inv]
  obtain ⟨u, _, huniq⟩ := existsUnique_positiveRealCharacter_freq (j.val.1.comp τ)
  have hsj : s j = β - t₀ k ω + a * n := by
    apply (huniq (s j) ?_).trans (huniq (β - t₀ k ω + a * n) ?_).symm
    · intro t
      change j.val.1 (τ t) = _
      rw [hξ, h₀, one_mul, hτ]
    · intro t
      change j.val.1 (τ t) = _
      rw [hj, hfreq, hτ]
      have hβt := hβ t
      change χ ω (τ t) = _ at hβt
      rw [hβt, ← Circle.exp_add]
      congr 1
      ring
  have hsz : 1 + |s j| ≤ A₀ * (1 + |(n : ℝ)|) := by
    have htri := abs_add_le (β - t₀ k ω) (a * (n : ℝ))
    rw [← hsj, abs_mul] at htri
    dsimp [A₀]
    nlinarith [abs_nonneg (β - t₀ k ω), abs_nonneg a, abs_nonneg (n : ℝ),
      mul_nonneg (abs_nonneg (β - t₀ k ω)) (abs_nonneg (n : ℝ))]
  exact (hqC j).trans (by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsz p) hC.le)

open Classical in
/-- Theorem 4.6.1.5, pp. 211–217. Commensurability is imposed on the
logarithmic periods. A moment outside its multiplicity is extended by zero
on the corresponding cyclic lattice. -/
public theorem periodicMomentBases_corrected (hN : 0 < N)
    (hχ : ∀ (ω' : PontryaginDual K) (u : K), χ ω' u.val = ω' u)
    (hperiods : ∃ a : ℝ, 0 < a ∧ ∀ k, ∃ r : ℚ, (period (γs k)) = (r : ℝ) * a) :
    IsDiscrete (modulatedPeriodicSpectrum m ω γs) ∧ Nonempty (ℕ ≃ J) ∧
      (∃ ψ : J → U,
        (∀ σ : ℕ ≃ J,
          let e := ψ ∘ σ
          let d := D ∘ σ
          let ev : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
            fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
          IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d ∧
            IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev) ∧
        ∀ q : Seminorm ℂ U, Continuous q →
          ∃ d : ℕ, ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧
            ∀ (n : ℤ) (j : J), j.val.1 = freq[k, n] →
              q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d) ∧
      ∀ (f : modulatedDecayIsotype m univ (mem_univ 0) ω) (r k : Fin N),
        ∃ v : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
          v (Multiplicative.ofAdd n) =
            if r.val < modulatedPeriodicMultiplicity m ω γs (freq[k, n]) then
              modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ)
                (freq[k, n]) r.val f
            else 0 := by
  refine ⟨modulatedPeriodicSpectrum_isDiscrete m hm ω γs hγs,
    modulatedPeriodicMomentIndex_enumerable m hm hms ω γs hγs hN, ?_, ?_⟩
  · obtain ⟨ψ, hbi⟩ := modulatedQuotientLogMoment_bases_biorthogonal
      (m := m) (hm := hm) (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ)
      (hcomm := hperiods)
    refine ⟨ψ, fun σ ↦ ?_, fun q hq ↦ ?_⟩
    · have hb := modulatedQuotientLogMoment_bases_quotient
        (m := m) (hm := hm) (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ)
        (hcomm := hperiods) σ ψ hbi
      have ha := modulatedQuotientLogMoment_bases_absolute
        (m := m) (hm := hm) (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) σ ψ hb
      exact ⟨hb, ha, modulatedQuotientLogMoment_bases_dual
        (m := m) (hm := hm) (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ)
        (hcomm := hperiods) σ ψ hb ha⟩
    · exact modulatedQuotientLogMoment_growth_corrected
        m hm hms ω γs hγs μ χ t₀ ht₀ hperiods ψ hbi q hq
  · intro f r k
    exact modulatedLogMoment_lattice_schwartz
      (m := m) (hm := hm) (hms := hms) (ω := ω) (γs := γs) (hγs := hγs)
      (μ := μ) (χ := χ) (hχ := hχ) (t₀ := t₀) (ht₀ := ht₀) f r k

#print axioms periodicMomentBases_corrected
#print axioms Printed.modulatedQuotientLogMoment_biorthogonal_basis_false

end Modulated

end

end RiemannMasullo
