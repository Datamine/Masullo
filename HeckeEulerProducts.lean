/-
The ideal-norm convergence proof adapts the Apache-2.0 RiemannMasullo project,
commit cd84b23dd5e4f741037cf31aee06bc90161c6514. See External/PROVENANCE.md.
-/
import Ideles
import GammaStripBounds
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Valuation.Discrete.RankOne

open NumberField Filter Ideal Set Topology IsDedekindDomain
open scoped NumberField RestrictedProduct

namespace Masullo

noncomputable section

/-- The Dirichlet series defining Dedekind zeta converges absolutely to the right of one. -/
theorem dedekindZeta_LSeriesSummable (F : Type*) [Field F] [NumberField F] {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // I.absNorm = n} : ℂ)) s := by
  -- The nonzero residue gives a point of convergence to the left of any given exponent.
  have hres := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).eventually_ne
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  obtain ⟨t, ht, ht'⟩ := (hres.and (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs))).exists
  apply LSeriesSummable.of_re_le_re (s := (t : ℂ)) ht'.le
  by_contra hdiv
  exact ht (by rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ hdiv, mul_zero])

/-- The sum of inverse powers of integral ideal norms converges for each real exponent above one. -/
theorem summable_absNorm_rpow (F : Type*) [Field F] [NumberField F] {r : ℝ} (hr : 1 < r) :
    Summable fun I : Ideal (𝓞 F) ↦ (I.absNorm : ℝ) ^ (-r) := by
  classical
  let A (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // I.absNorm = n}
  have hsum : Summable (fun n : ℕ ↦ A n * (n : ℝ) ^ (-r)) := by
    apply (dedekindZeta_LSeriesSummable F (s := (r : ℂ)) hr).norm.congr
    intro n
    obtain rfl | hn := eq_or_ne n 0
    · simp [Real.zero_rpow (by linarith : -r ≠ 0)]
    · simp [hn, A, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 F))).summable_iff]
  have (n : ℕ) : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).to_subtype
  refine (summable_sigma_of_nonneg (fun _ ↦ by dsimp; positivity)).2
    ⟨fun _ ↦ Summable.of_finite, hsum.congr fun n ↦ ?_⟩
  change _ = ∑' I : {I : Ideal (𝓞 F) // I.absNorm = n}, (I.val.absNorm : ℝ) ^ (-r)
  rw [tsum_congr (fun I : {I : Ideal (𝓞 F) // I.absNorm = n} ↦
    congrArg (fun m : ℕ ↦ (m : ℝ) ^ (-r)) I.property)]
  simp [A, tsum_const, nsmul_eq_mul]


variable (F : Type*) [Field F] [NumberField F]

/-- The idele supported at a single finite place, with all other components one. -/
def singleFiniteIdele (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    Idele F := by
  classical
  let f (x : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
    ⟨Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v x, by
      have h : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, w ≠ v := by
        rw [Filter.eventually_cofinite]
        simpa using Set.finite_singleton v
      filter_upwards [h] with w hw
      rw [Function.update_of_ne hw]
      exact (w.adicCompletionIntegers F).one_mem⟩
  have hf (x : v.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) :
      f x w = Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v x w := rfl
  refine ⟨(1, f (u : v.adicCompletion F)), (1, f ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
    ?_, ?_⟩
  all_goals
    apply Prod.ext (by change (1 : InfiniteAdeleRing F) * 1 = 1; simp)
    apply DFunLike.ext
    intro w
    first
    | change f (u : v.adicCompletion F) w * f (↑u⁻¹ : v.adicCompletion F) w = 1
    | change f (↑u⁻¹ : v.adicCompletion F) w * f (u : v.adicCompletion F) w = 1
    simp only [hf]
    by_cases hw : w = v
    · subst w
      simp
    · simp [Function.update_of_ne hw]

theorem singleFiniteIdele_norm (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ideleNorm F (singleFiniteIdele F v u) = ‖(u : v.adicCompletion F)‖ := by
  classical
  let d := singleFiniteIdele F v u
  change (∏ w : InfinitePlace F, ‖d.val.1 w‖ ^ w.mult) *
      (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖d.val.2 w‖) = _
  have h₁ (w : InfinitePlace F) : d.val.1 w = 1 := rfl
  have h₂ (w : HeightOneSpectrum (𝓞 F)) :
      d.val.2 w = Function.update (fun w : HeightOneSpectrum (𝓞 F) =>
        (1 : w.adicCompletion F)) v (u : v.adicCompletion F) w := rfl
  simp only [h₁, norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v (fun w hw => by rw [h₂, Function.update_of_ne hw, norm_one]),
    h₂, Function.update_self]

theorem singleFiniteIdele_mul (v : HeightOneSpectrum (𝓞 F)) (u w : (v.adicCompletion F)ˣ) :
    singleFiniteIdele F v (u * w) = singleFiniteIdele F v u * singleFiniteIdele F v w := by
  classical
  apply Units.ext
  apply Prod.ext (by change 1 = (1 : InfiniteAdeleRing F) * 1; simp)
  apply DFunLike.ext
  intro i
  let a (z : v.adicCompletion F) :=
    Function.update (fun j : HeightOneSpectrum (𝓞 F) => (1 : j.adicCompletion F)) v z
  change a (↑(u * w)) i = a ↑u i * a ↑w i
  by_cases hi : i = v
  · subst i
    simp [a]
  · simp [a, Function.update_of_ne hi]

/-- A generator of the completed valuation's maximal ideal has the stated
normalized local absolute value. -/
theorem norm_finiteUniformizer (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hv : Valued.v.IsUniformizer x) : ‖x‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  have he : Valued.v x = WithZero.exp (-1 : ℤ) := hv.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective F v)))
  rw [FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  change (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) = _
  simp

def chosenFiniteUniformizer (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ :=
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero

theorem chosenFiniteUniformizer_spec (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v.IsUniformizer (chosenFiniteUniformizer F v : v.adicCompletion F) := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  exact val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec

/-- Unramified means that the local character is trivial on the local integer-ring units. -/
def unramifiedFiniteCharacter (χ : PontryaginDual (IdeleClass F))
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ u : (v.adicCompletion F)ˣ, ‖(u : v.adicCompletion F)‖ = 1 →
    χ (ideleClassMap F (singleFiniteIdele F v u)) = 1

/-- Changing the uniformizer multiplies it by a unit on which the local character is trivial. -/
theorem unramifiedFiniteCharacter_uniformizer_eq (χ : PontryaginDual (IdeleClass F))
    (v : HeightOneSpectrum (𝓞 F)) (hχ : unramifiedFiniteCharacter F χ v)
    (π ϖ : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (hϖ : Valued.v.IsUniformizer (ϖ : v.adicCompletion F)) :
    χ (ideleClassMap F (singleFiniteIdele F v π)) =
      χ (ideleClassMap F (singleFiniteIdele F v ϖ)) := by
  let u := π * ϖ⁻¹
  have hu : ‖(u : v.adicCompletion F)‖ = 1 := by
    have hn : ‖(ϖ : v.adicCompletion F)‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero ϖ)
    change ‖(π : v.adicCompletion F) * ↑ϖ⁻¹‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_mul, norm_inv,
      show ‖(π : v.adicCompletion F)‖ = ‖(ϖ : v.adicCompletion F)‖ by
        rw [norm_finiteUniformizer F v _ hπ, norm_finiteUniformizer F v _ hϖ],
      mul_inv_cancel₀ hn]
  have hprod : π = u * ϖ := by simp [u]
  calc
    _ = χ (ideleClassMap F (singleFiniteIdele F v (u * ϖ))) :=
      congrArg (fun w => χ (ideleClassMap F (singleFiniteIdele F v w))) hprod
    _ = _ := by rw [singleFiniteIdele_mul, map_mul, map_mul, hχ u hu, one_mul]

/-- An unramified factor is read on a chosen uniformizer. Ramified places
have coefficient zero, so their factor is one. -/
def heckeEulerCoefficient (χ : PontryaginDual (IdeleClass F))
    (π : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  open Classical in
  if unramifiedFiniteCharacter F χ v
  then χ (ideleClassMap F (singleFiniteIdele F v (π v)))
  else 0

theorem norm_heckeEulerCoefficient_le_one (χ : PontryaginDual (IdeleClass F))
    (π : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ‖heckeEulerCoefficient F χ π v‖ ≤ 1 := by
  classical
  unfold heckeEulerCoefficient
  split_ifs
  · simp only [Circle.norm_coe, le_rfl]
  · simp

def heckeEulerFactor (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  (1 - c v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹

/-- At an unramified prime the reciprocal factor is one minus the norm
twist evaluated on the local uniformizer. -/
theorem heckeEulerFactor_inv_uniformizer (χ : PontryaginDual (IdeleClass F))
    (π : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hπ : Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hv : unramifiedFiniteCharacter F χ v) (s : ℂ) :
    (heckeEulerFactor F (heckeEulerCoefficient F χ π) v s)⁻¹ =
      1 - (χ (ideleClassMap F (singleFiniteIdele F v (π v))) : ℂ) *
        (ideleClassNorm F (ideleClassMap F (singleFiniteIdele F v (π v))) : ℂ) ^ s := by
  classical
  rw [heckeEulerFactor, inv_inv, heckeEulerCoefficient, if_pos hv, ideleClassNorm_mk,
    singleFiniteIdele_norm, norm_finiteUniformizer F v _ hπ, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _), Complex.cpow_neg, Complex.ofReal_natCast]

private theorem heckeEulerFactor_estimate (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (v : HeightOneSpectrum (𝓞 F)) {r : ℝ} (hr : 1 < r)
    {s : ℂ} (hs : r ≤ s.re) :
    1 / 2 ≤ ‖1 - c v * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ ∧
    ‖heckeEulerFactor F c v s - 1‖ ≤ 2 * (v.asIdeal.absNorm : ℝ) ^ (-r) := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 2 ≤ q := by
    have hv : 2 ≤ v.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm v
    dsimp [q]
    exact_mod_cast hv
  have hq₁ : 1 ≤ q := by linarith
  have hq₀ : 0 < q := by linarith
  let z := c v * (q : ℂ) ^ (-s)
  have hcomp : ‖z‖ ≤ q ^ (-r) := by
    rw [show ‖z‖ = ‖c v‖ * q ^ (-s.re) by
      simp only [z, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re]]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hq₀.le _) (hc v)).trans
      (Real.rpow_le_rpow_of_exponent_le hq₁ (by linarith))
  have hhalf : q ^ (-r) ≤ 1 / 2 := by
    calc
      q ^ (-r) ≤ q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq₁ (by linarith)
      _ = 1 / q := by rw [Real.rpow_neg hq₀.le, Real.rpow_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
  have hd : 1 / 2 ≤ ‖1 - z‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at ht
    linarith
  have hn : 1 - z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  change 1 / 2 ≤ ‖1 - z‖ ∧ ‖(1 - z)⁻¹ - 1‖ ≤ 2 * q ^ (-r)
  refine ⟨hd, ?_⟩
  rw [show (1 - z)⁻¹ - 1 = z / (1 - z) by field_simp; ring, norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - z‖)).mpr
  calc
    ‖z‖ ≤ q ^ (-r) := hcomp
    _ = (2 * q ^ (-r)) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

theorem heckeEulerFactor_summableUniformlyOn (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (K : Set ℂ) (hK : IsCompact K) (h : ∀ s ∈ K, 1 < s.re) :
    SummableUniformlyOn (fun v s ↦ ‖heckeEulerFactor F c v s - 1‖) K := by
  obtain ⟨r, hr, hmin⟩ : ∃ r : ℝ, 1 < r ∧ ∀ s ∈ K, r ≤ s.re := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨2, by norm_num, by simp⟩
    · obtain ⟨s, hs, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
      exact ⟨s.re, h s hs, fun x hx ↦ hmin hx⟩
  have hu : Summable fun v : HeightOneSpectrum (𝓞 F) ↦ (v.asIdeal.absNorm : ℝ) ^ (-r) :=
    (summable_absNorm_rpow F hr).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  apply (HasSumUniformlyOn.of_norm_le_summable (hu.mul_left 2) _).summableUniformlyOn
  intro v s hs
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact (heckeEulerFactor_estimate F c hc v hr (hmin s hs)).2

/-- The absolutely convergent finite Hecke Euler product is nonzero in its
half-plane of convergence. -/
theorem heckeEulerProduct_ne_zero (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∏' v, heckeEulerFactor F c v s) ≠ 0 := by
  let f v := heckeEulerFactor F c v s - 1
  have hf (v) : 1 + f v = heckeEulerFactor F c v s := by dsimp [f]; ring
  have hu : Summable fun v : HeightOneSpectrum (𝓞 F) ↦ (v.asIdeal.absNorm : ℝ) ^ (-s.re) :=
    (summable_absNorm_rpow F hs).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hsum : Summable (‖f ·‖) :=
    (hu.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) fun v =>
      (heckeEulerFactor_estimate F c hc v hs le_rfl).2
  have hn : ∀ v, 1 + f v ≠ 0 := by
    intro v
    rw [hf]
    apply inv_ne_zero
    exact norm_ne_zero_iff.mp (by
      linarith [(heckeEulerFactor_estimate F c hc v hs le_rfl).1])
  simpa only [hf] using tprod_one_add_ne_zero_of_summable hn hsum

theorem heckeEulerProduct_hasProdUniformlyOn (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (K : Set ℂ) (hK : IsCompact K) (h : ∀ s ∈ K, 1 < s.re) :
    HasProdUniformlyOn (heckeEulerFactor F c)
      (fun s => ∏' v, heckeEulerFactor F c v s) K := by
  obtain ⟨r, hr, hmin⟩ : ∃ r : ℝ, 1 < r ∧ ∀ s ∈ K, r ≤ s.re := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨2, by norm_num, by simp⟩
    · obtain ⟨s, hs, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
      exact ⟨s.re, h s hs, fun x hx ↦ hmin hx⟩
  have hu : Summable fun v : HeightOneSpectrum (𝓞 F) ↦ (v.asIdeal.absNorm : ℝ) ^ (-r) :=
    (summable_absNorm_rpow F hr).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hcts (v : HeightOneSpectrum (𝓞 F)) :
      ContinuousOn (fun s => heckeEulerFactor F c v s - 1) K := by
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    letI : NeZero (v.asIdeal.absNorm : ℂ) := ⟨hq⟩
    have hpow : Continuous (fun s : ℂ => (v.asIdeal.absNorm : ℂ) ^ (-s)) :=
      (differentiable_const_cpow_of_neZero _).continuous.comp continuous_neg
    apply ContinuousOn.sub _ continuousOn_const
    apply (continuousOn_const.sub (continuous_const.mul hpow).continuousOn).inv₀
    intro x hx
    change 1 - c v * (v.asIdeal.absNorm : ℂ) ^ (-x) ≠ 0
    exact norm_ne_zero_iff.mp (by
      have hb := (heckeEulerFactor_estimate F c hc v hr (hmin x hx)).1
      linarith)
  have H := Summable.hasProdUniformlyOn_one_add (f := fun v s => heckeEulerFactor F c v s - 1)
    hK (hu.mul_left 2) (Eventually.of_forall fun v s hs =>
      (heckeEulerFactor_estimate F c hc v hr (hmin s hs)).2) hcts
  simpa only [add_comm (1 : ℂ), sub_add_cancel] using H

/-- The shifts and parities of the infinite local factors of a unitary character. -/
structure HeckeInfiniteParameters where
  radial : InfinitePlace F → ℝ
  parity : InfinitePlace F → Fin 2
  angular : InfinitePlace F → ℤ

def heckeInfiniteGamma (a : HeckeInfiniteParameters F) (s : ℂ) : ℂ :=
  open Classical in
  ∏ v : InfinitePlace F,
    if v.IsReal then Complex.Gammaℝ (s + Complex.I * (a.radial v : ℂ) + (a.parity v).val)
    else Complex.Gammaℂ (s + Complex.I * (a.radial v : ℂ) + (a.angular v).natAbs / 2) / 2

open scoped Asymptotics in
/-- On any fixed closed strip the reciprocal of the actual archimedean
Euler product grows at most exponentially in absolute height.
The product argument adapts the original proof at ab046ba. -/
theorem heckeInfiniteGamma_inv_isBigO_exp (a : HeckeInfiniteParameters F) (lo hi : ℝ) :
    (fun s => (heckeInfiniteGamma F a s)⁻¹) =O[
      comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc lo hi)]
      (fun s => Real.exp ((Fintype.card (InfinitePlace F) * Real.pi) * |s.im|)) := by
  classical
  let l := comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc lo hi)
  let P (v : InfinitePlace F) (s : ℂ) :=
    (if v.IsReal then Complex.Gammaℝ (s + Complex.I * (a.radial v : ℂ) + (a.parity v).val)
      else Complex.Gammaℂ (s + Complex.I * (a.radial v : ℂ) + (a.angular v).natAbs / 2) / 2)⁻¹
  have hP (v : InfinitePlace F) : P v =O[l] fun s => Real.exp (Real.pi * |s.im|) := by
    by_cases hv : v.IsReal
    · let w := Complex.I * (a.radial v : ℂ) + (a.parity v).val
      have h : P v =O[l] fun s => Real.exp ((Real.pi / 2) * |s.im|) := by
        simpa only [P, ite_eq_left hv, w, add_assoc] using inv_Gammaℝ_add_isBigO_exp lo hi w
      refine h.trans (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s => ?_))
      simp only [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
      gcongr
      linarith [Real.pi_pos]
    · let w := Complex.I * (a.radial v : ℂ) + (a.angular v).natAbs / 2
      have h := ((inv_Gammaℝ_add_isBigO_exp lo hi w).mul
        (inv_Gammaℝ_add_isBigO_exp lo hi (w + 1))).const_mul_left (2 : ℂ)
      have hLocal (s : ℂ) : P v s =
          2 * ((Complex.Gammaℝ (s + w))⁻¹ * (Complex.Gammaℝ (s + (w + 1)))⁻¹) := by
        simp only [P, ite_eq_right hv, w, ← add_assoc, div_eq_mul_inv, mul_inv_rev, inv_inv,
          ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
        ring
      simpa only [← hLocal, ← Real.exp_add, ← add_mul, add_halves] using h
  have hProd := Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun v _ => hP v)
  simpa only [P, heckeInfiniteGamma, Finset.prod_inv_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_nat_mul, mul_assoc] using hProd

theorem differentiableAt_heckeInfiniteGamma (a : HeckeInfiniteParameters F) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (heckeInfiniteGamma F a) s := by
  classical
  have hR {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Complex.Gammaℝ z := by
    have h := Complex.differentiable_Gammaℝ_inv.differentiableAt (x := z)
    have hh := h.inv (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz))
    change DifferentiableAt ℂ (fun t => ((Complex.Gammaℝ t)⁻¹)⁻¹) z at hh
    simpa only [inv_inv] using hh
  have hC {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Complex.Gammaℂ z := by
    have hn : Complex.Gammaℂ z ≠ 0 := by
      rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
      exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
        (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; positivity))
    have hh := (Complex.differentiable_Gammaℂ_inv.differentiableAt (x := z)).inv (inv_ne_zero hn)
    change DifferentiableAt ℂ (fun t => ((Complex.Gammaℂ t)⁻¹)⁻¹) z at hh
    simpa only [inv_inv] using hh
  unfold heckeInfiniteGamma
  apply DifferentiableAt.fun_finsetProd
  intro v _
  split_ifs
  · let t (z : ℂ) := z + Complex.I * (a.radial v : ℂ) + (a.parity v).val
    have ht : DifferentiableAt ℂ t s := by dsimp [t]; fun_prop
    have hz : 0 < (t s).re := by
      simp [t, Complex.mul_re]
      positivity
    exact (hR hz).comp s ht
  · let t (z : ℂ) := z + Complex.I * (a.radial v : ℂ) + (a.angular v).natAbs / 2
    have ht : DifferentiableAt ℂ t s := by dsimp [t]; fun_prop
    have hz : 0 < (t s).re := by
      simp [t, Complex.mul_re, Complex.div_ofNat_re]
      positivity
    exact ((hC hz).comp s ht).div_const 2

/-- The actual finite idele-class character factors converge absolutely and
locally uniformly, and multiplying by the archimedean gamma product preserves
local uniform convergence on the half-plane of absolute convergence. -/
theorem completedHeckeEulerProduct_uniform (χ : PontryaginDual (IdeleClass F))
    (π : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (a : HeckeInfiniteParameters F) (K : Set ℂ) (hK : IsCompact K)
    (h : ∀ s ∈ K, 1 < s.re) :
    SummableUniformlyOn (fun v s => ‖heckeEulerFactor F (heckeEulerCoefficient F χ π) v s - 1‖) K ∧
    TendstoUniformlyOn
      (fun S : Finset (HeightOneSpectrum (𝓞 F)) => fun s =>
        heckeInfiniteGamma F a s * ∏ v ∈ S, heckeEulerFactor F (heckeEulerCoefficient F χ π) v s)
      (fun s => heckeInfiniteGamma F a s * ∏' v, heckeEulerFactor F (heckeEulerCoefficient F χ π) v s)
      atTop K := by
  let c := heckeEulerCoefficient F χ π
  have hc : ∀ v, ‖c v‖ ≤ 1 := norm_heckeEulerCoefficient_le_one F χ π
  refine ⟨heckeEulerFactor_summableUniformlyOn F c hc K hK h, ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  have hu := hasProdUniformlyOn_iff_tendstoUniformlyOn.mp
    (heckeEulerProduct_hasProdUniformlyOn F c hc K hK h)
  have hG : ContinuousOn (fun s => ‖heckeInfiniteGamma F a s‖) K := fun s hs =>
    (differentiableAt_heckeInfiniteGamma F a (zero_lt_one.trans (h s hs))).continuousAt.norm.continuousWithinAt
  obtain ⟨b, _, hb⟩ := hK.exists_isMaxOn hne hG
  let B := ‖heckeInfiniteGamma F a b‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / B) (div_pos hε hB)] with T hT
  intro s hs
  have hbound : ‖heckeInfiniteGamma F a s‖ ≤ B := (hb hs).trans (by dsimp [B]; linarith)
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have hsmall := hT s hs
  rw [dist_eq_norm] at hsmall
  exact (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_left hsmall hB).trans_eq (mul_div_cancel₀ _ hB.ne'))

end
end Masullo
