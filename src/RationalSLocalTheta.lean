import SLocalCharacterRestriction
import SLocalBruhatProjections
import PrimePowerGrowth
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Asymptotics Classical NumberField RestrictedProduct SchwartzMap

namespace Masullo

noncomputable section

private theorem rationalSamplingWithEmpty (M : ℕ) (a : Fin M → ℝ) (ha : ∀ i, 1 < a i)
    (φ : ℝ → ℂ) (D : ℝ) (hD : 0 < D) (hb : ∀ t > 0, ‖φ t‖ ≤ D)
    (ht : ∀ t ≥ 1, ‖φ t‖ ≤ D / t ^ (2 : ℕ)) :
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧ ∀ t : ℝ, 0 < t → t < T →
      let term : (Fin M → ℕ) → ℝ := fun k => ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ C * |Real.log t| ^ M := by
  by_cases hM : 0 < M
  · exact product_power_sampling_bound hM (by decide : 1 < (2 : ℕ)) a ha φ hD hD zero_lt_one hb ht
  · obtain rfl : M = 0 := by omega
    refine ⟨1, D, zero_lt_one, hD, fun t ht₀ _ => ?_⟩
    refine ⟨Summable.of_finite, ?_⟩
    simp only [Fin.prod_univ_zero, one_mul, pow_zero, mul_one]
    rw [tsum_fintype, Fintype.sum_subsingleton _ (fun x : Fin 0 => Fin.elim0 x)]
    exact hb t ht₀

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

local notation "A" => SAdeles ℚ S
local notation "U" => (sIntegerRing ℚ S)ˣ
private def ratLocalUnit : U →* Aˣ :=
  ((sLocalIdeleNorm ℚ S).ker.subtype).comp (sPrincipalLocalNormOne ℚ S)
local notation "unitAtS" => ratLocalUnit S
local notation "ratNorm" => sLocalIdeleNorm ℚ S
local notation "w" => Rat.infinitePlace

/-- The rational S-idelic norm uses the single real place and all finite places in S. -/
private theorem rat_sIdeleNorm_eq (g : Aˣ) :
    ratNorm g = ‖g.val.1 w‖ * ∏ v : S, ‖g.val.2 v‖ := by
  classical
  let a := sLocalEmbed ℚ S g
  change ideleNorm ℚ a.val = _
  change (∏ v : InfinitePlace ℚ, ‖a.val.val.1 v‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖a.val.val.2 v‖) = _
  rw [Fintype.prod_subsingleton _ w, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  rw [show a.val.val.1 = g.val.1 from sLocalEmbed_arch ℚ S g]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra h
    have hord := (sIdeleBlock_mem_iff ℚ S a.val).mp a.property v h
    have hone : ‖a.val.val.2 v‖ = 1 := by
      rw [FinitePlace.norm_def, (ideleOrder_eq_zero_iff ℚ _ _).mp hord]
      simp
    exact hv hone), ← Finset.prod_attach]
  congr 1
  exact Finset.prod_congr rfl (fun v _ => congrArg norm (sLocalEmbed_finite ℚ S g v))

open scoped Classical in
/-- The archimedean norm of a rational adele is the norm of its unique real coordinate. -/
private theorem rat_arch_norm_eq (x : InfiniteAdeleRing ℚ) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x‖ = ‖x w‖ := by
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace, Finset.sup'_univ_eq_ciSup, ciSup_unique]
  change mixedEmbedding.normAtPlace w _ = _
  rw [mixedEmbedding.normAtPlace_apply_of_isReal Rat.isReal_infinitePlace,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) _

/-- Multiplying by a diagonal S-unit preserves the S-idelic norm. -/
private theorem rat_sIdeleNorm_unit_mul (g : Aˣ) (u : U) :
    ratNorm (unitAtS u * g) = ratNorm g := by
  have hu : sLocalIdeleNorm ℚ S (unitAtS u) = 1 :=
    (sPrincipalLocalNormOne ℚ S u).property
  rw [map_mul, hu, one_mul]

/-- Every finite coordinate of an S-idele is nonzero. -/
private theorem rat_sIdele_finite_ne_zero (g : Aˣ) (v : S) : g.val.2 v ≠ 0 := by
  let ev : A →+* v.val.adicCompletion ℚ :=
    (Pi.evalRingHom _ v).comp (RingHom.snd _ _)
  exact (g.isUnit.map ev).ne_zero

/-- Among diagonal S-unit multiples, the finite norms and the sign of the
rational multiplier determine the multiplier. -/
private theorem rat_sUnit_eq_of_norms (g : Aˣ) {u z : U}
    (hfin : ∀ v : S, ‖(unitAtS u * g).val.2 v‖ = ‖(unitAtS z * g).val.2 v‖)
    (hsign : (0 ≤ (u.val.val : ℚ)) ↔ (0 ≤ (z.val.val : ℚ))) : u = z := by
  have hnorm := (rat_sIdeleNorm_unit_mul S g u).trans (rat_sIdeleNorm_unit_mul S g z).symm
  rw [rat_sIdeleNorm_eq, rat_sIdeleNorm_eq] at hnorm
  simp_rw [hfin] at hnorm
  have hprod := Finset.prod_pos (s := Finset.univ) fun v _ ↦
    norm_pos_iff.mpr (rat_sIdele_finite_ne_zero S (unitAtS z * g) v)
  have hinf := (mul_right_cancel₀ hprod.ne') hnorm
  have harch (ξ : U) :
      ‖(unitAtS ξ * g).val.1 w‖ = |(ξ.val.val : ℚ)| * ‖g.val.1 w‖ := by
    change ‖algebraMap ℚ Rat.infinitePlace.Completion ξ.val.val * g.val.1 w‖ = _
    rw [norm_mul, eq_ratCast (algebraMap ℚ Rat.infinitePlace.Completion),
      InfinitePlace.Completion.Rat.norm_infinitePlace_completion]
  rw [harch, harch] at hinf
  let ev : A →+* Rat.infinitePlace.Completion :=
    (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  have hne : g.val.1 w ≠ 0 := (g.isUnit.map ev).ne_zero
  have habs : |u.val.val| = |z.val.val| :=
    Rat.cast_injective (mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) hinf)
  apply Units.ext
  apply Subtype.ext
  by_cases hu : 0 ≤ u.val.val
  · rwa [abs_of_nonneg hu, abs_of_nonneg (hsign.mp hu)] at habs
  · have hz : ¬ 0 ≤ z.val.val := mt hsign.mpr hu
    simpa [abs_of_neg (lt_of_not_ge hu), abs_of_neg (lt_of_not_ge hz)] using habs

/-- A nonzero finite coordinate has norm given by an integer power of its
residue field cardinality. -/
private theorem rat_finite_norm_eq_zpow (v : S) (x : v.val.adicCompletion ℚ)
    (hx : x ≠ 0) : ∃ e : ℤ, ‖x‖ = (v.val.asIdeal.absNorm : ℝ) ^ e := by
  refine ⟨Multiplicative.toAdd (WithZero.unzero (Valued.v.ne_zero_iff.mpr hx)), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
    (Valued.v.ne_zero_iff.mpr hx)]
  rfl


/-- Finite norm cutoffs put the translated rational S-units into an integer
grid with a shift independent of the idele. The sign distinguishes opposite units. -/
private theorem rat_sUnit_grid (R : S → ℝ) (e : Fin S.card ≃ S) :
    let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
    ∃ Q : ℝ, 0 < Q ∧ ∀ g : Aˣ,
      let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
      ∃ index : P ↪ Bool × (Fin S.card → ℕ), ∀ u : P,
        ‖(unitAtS u.val * g).val.1 w‖ * Q =
          (∏ i, q i ^ (index u).2 i) * ratNorm g := by
  classical
  let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
  have hq (i) : 1 < q i := by
    simpa only [q, Nat.one_lt_cast] using HeightOneSpectrum.one_lt_absNorm (e i).val
  have hqpos (i) : 0 < q i := zero_lt_one.trans (hq i)
  choose N hN using fun i ↦ pow_unbounded_of_one_lt (R (e i)) (hq i)
  let Q := ∏ i, q i ^ N i
  refine ⟨Q, Finset.prod_pos (fun i _ ↦ pow_pos (hqpos i) _), fun g ↦ ?_⟩
  let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
  let y (u : P) := unitAtS u.val * g
  have hdiscrete (u : P) (i : Fin S.card) :
      ∃ a : ℤ, ‖(y u).val.2 (e i)‖ = q i ^ a :=
    rat_finite_norm_eq_zpow S (e i) _ (rat_sIdele_finite_ne_zero S (y u) (e i))
  choose a ha using hdiscrete
  let n (u : P) (i : Fin S.card) : ℕ := (↑(N i) - a u i).toNat
  have hshift (u : P) (i : Fin S.card) :
      ‖(y u).val.2 (e i)‖ * q i ^ n u i = q i ^ N i := by
    have hle : a u i ≤ (N i : ℤ) := by
      apply (zpow_right_strictMono₀ (hq i)).le_iff_le.mp
      rw [← ha u i, zpow_natCast]
      exact (u.property (e i)).trans (hN i).le
    rw [ha, ← zpow_natCast (q i) (n u i), ← zpow_add₀ (hqpos i).ne',
      Int.toNat_sub_of_le hle, add_sub_cancel, zpow_natCast]
  let index : P ↪ Bool × (Fin S.card → ℕ) :=
    ⟨fun u ↦ (decide (0 ≤ (u.val.val.val : ℚ)), n u), by
      intro u z h
      apply Subtype.ext
      apply rat_sUnit_eq_of_norms S g
      · intro v
        obtain ⟨i, rfl⟩ := e.surjective v
        have hn : n u i = n z i := congrFun (congrArg Prod.snd h) i
        apply mul_right_cancel₀ (pow_ne_zero (n u i) (hqpos i).ne')
        calc
          _ = q i ^ N i := hshift u i
          _ = ‖(y z).val.2 (e i)‖ * q i ^ n z i := (hshift z i).symm
          _ = _ := by rw [hn]
      · exact decide_eq_decide.mp (congrArg Prod.fst h)⟩
  refine ⟨index, fun u ↦ ?_⟩
  have hQ : (∏ v : S, ‖(y u).val.2 v‖) * (∏ i, q i ^ n u i) = Q := by
    rw [← e.prod_comp (fun v ↦ ‖(y u).val.2 v‖), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ ↦ hshift u i)
  change ‖(y u).val.1 w‖ * Q = (∏ i, q i ^ n u i) * ratNorm g
  rw [← hQ, ← mul_assoc, ← rat_sIdeleNorm_eq, rat_sIdeleNorm_unit_mul, mul_comm]

/-- Compact finite support and quadratic archimedean decay suffice for the
logarithmic growth bound on the sum over rational S-units. -/
private theorem rat_sUnit_sum_norm_log_growth (f : A → ℂ) (R : S → ℝ) (B₀ B₂ : ℝ)
    (hR : ∀ x, (¬ ∀ v, ‖x.2 v‖ ≤ R v) → f x = 0)
    (h₀ : ∀ x, ‖f x‖ ≤ B₀)
    (h₂ : ∀ x, ‖f x‖ * ‖x.1 w‖ ^ 2 ≤ B₂) :
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧ ∀ g : Aˣ, ratNorm g < T →
      (∑' u : U, ‖f (unitAtS u * g).val‖) ≤ C * |Real.log (ratNorm g)| ^ S.card := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
  have hq (i) : 1 < q i := by
    simpa only [q, Nat.one_lt_cast] using HeightOneSpectrum.one_lt_absNorm (e i).val
  obtain ⟨Q, _, hgrid⟩ := rat_sUnit_grid S R e
  let D := max 1 (max B₀ (B₂ * Q ^ 2))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  let φ (t : ℝ) : ℂ := (D * ((max 1 t) ^ 2)⁻¹ : ℝ)
  have hφ (t : ℝ) : ‖φ t‖ = D * ((max 1 t) ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  obtain ⟨T, C, hT, hC, hseries⟩ := rationalSamplingWithEmpty S.card q hq φ D hD
    (fun t _ => by
      rw [hφ]
      have hp : 1 ≤ (max 1 t) ^ 2 := one_le_pow₀ (le_max_left _ _)
      exact mul_le_of_le_one_right hD.le ((inv_le_one₀ (zero_lt_one.trans_le hp)).mpr hp))
    (fun t ht => by rw [hφ, max_eq_right ht, div_eq_mul_inv])
  refine ⟨T, 2 * C, hT, by positivity, fun g hg => ?_⟩
  have hng : 0 < ratNorm g := ideleNorm_pos ℚ (sLocalEmbed ℚ S g).val
  obtain ⟨hseriesSummable, hseriesBound⟩ := hseries (ratNorm g) hng hg
  let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
  obtain ⟨index, hindex⟩ := hgrid g
  let term (u : U) := f (unitAtS u * g).val
  let majorant (k : Fin S.card → ℕ) := ‖φ ((∏ i, q i ^ k i) * ratNorm g)‖
  have hpoint (u : P) : ‖term u.val‖ ≤ majorant (index u).2 := by
    let x := (unitAtS u.val * g).val
    change ‖f x‖ ≤ _
    dsimp only [majorant]
    rw [← hindex u, hφ]
    change ‖f x‖ ≤ D * ((max 1 (‖x.1 w‖ * Q)) ^ 2)⁻¹
    rcases le_total (‖x.1 w‖ * Q) 1 with hx | hx
    · rw [max_eq_left hx, one_pow, inv_one, mul_one]
      exact (h₀ x).trans
        ((le_max_left B₀ (B₂ * Q ^ 2)).trans (le_max_right 1 _))
    · rw [max_eq_right hx, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hx) _)).mpr
      rw [mul_pow, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right (h₂ x) (sq_nonneg Q)).trans
        ((le_max_right B₀ (B₂ * Q ^ 2)).trans (le_max_right 1 _))
  have hs : Summable majorant := hseriesSummable
  have hp : Summable (fun p : Bool × (Fin S.card → ℕ) ↦ majorant p.2) := by
    exact (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
      ⟨fun _ ↦ hs, Summable.of_finite⟩
  have hsub : Summable (fun u : P ↦ ‖term u.val‖) :=
    (hp.comp_injective index.injective).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hpoint
  have hsupport : Function.support (fun u ↦ ‖term u‖) ⊆ P :=
    Function.support_subset_iff'.mpr fun u hu ↦
      norm_eq_zero.mpr (hR _ hu)
  change (∑' u, ‖term u‖) ≤ (2 * C) * |Real.log (ratNorm g)| ^ S.card
  calc
    _ = ∑' u : P, ‖term u.val‖ := (tsum_subtype_eq_of_support_subset hsupport).symm
    _ ≤ ∑' p : Bool × (Fin S.card → ℕ), majorant p.2 :=
      hsub.tsum_le_tsum_of_inj index index.injective (fun _ _ ↦ norm_nonneg _) hpoint hp
    _ = 2 * (∑' k, majorant k) := by
      rw [hp.tsum_prod, tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_nsmul, two_mul]
    _ ≤ (2 * C) * |Real.log (ratNorm g)| ^ S.card := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hseriesBound (by positivity)


/-- The actual rational S-adele Schwartz–Bruhat test functions are the linear
span of archimedean Schwartz functions times finite-place locally constant
functions of compact support, on the product of the specified completions. -/
def rationalSLocalTestFunctions : Submodule ℂ (A → ℂ) :=
  Submodule.span ℂ {f | ∃ (φ : 𝓢(mixedEmbedding.mixedSpace ℚ, ℂ))
    (ψ : locallyConstantTests ((v : S) → v.val.adicCompletion ℚ)),
      f = fun a => φ (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ a.1) * ψ.val a.2}

private theorem rationalSLocalTest_bounds {f : A → ℂ}
    (hf : f ∈ rationalSLocalTestFunctions S) :
    Continuous f ∧
    (∃ R : S → ℝ, ∀ x, (¬ ∀ v, ‖x.2 v‖ ≤ R v) → f x = 0) ∧
    ∀ k : ℕ, ∃ B : ℝ, ∀ x, ‖f x‖ * ‖x.1 w‖ ^ k ≤ B := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, ψ, rfl⟩ := hf
    refine ⟨(φ.continuous.comp ((infiniteAdele_toMixed_continuous ℚ).comp continuous_fst)).mul
      (ψ.property.1.continuous.comp continuous_snd), ?_, ?_⟩
    · have hc : ∀ v : S, ∃ R : ℝ, ∀ a ∈ tsupport ψ.val, ‖a v‖ ≤ R := fun v =>
        ψ.property.2.exists_bound_of_continuousOn (continuous_apply v).continuousOn
      choose R hR using hc
      refine ⟨R, fun x hx => ?_⟩
      have hz : ψ.val x.2 = 0 := by
        by_contra! hn
        exact hx (fun v => hR v x.2 (subset_tsupport ψ.val hn))
      simp only [hz, mul_zero]
    · intro k
      let C : ℝ := SchwartzMap.seminorm ℂ k 0 φ
      obtain ⟨B, hB⟩ := ψ.property.2.exists_bound_of_continuousOn ψ.property.1.continuous.continuousOn
      refine ⟨max B 0 * C, fun x => ?_⟩
      have hBound : ‖ψ.val x.2‖ ≤ max B 0 := by
        by_cases hx : x.2 ∈ tsupport ψ.val
        · exact (hB _ hx).trans (le_max_left _ _)
        · have hz : ψ.val x.2 = 0 := notMem_support.mp (fun h => hx (subset_tsupport _ h))
          rw [hz, norm_zero]
          exact le_max_right _ _
      rw [norm_mul, mul_comm _ ‖ψ.val x.2‖, mul_assoc, ← rat_arch_norm_eq]
      apply mul_le_mul hBound _ (by positivity) (le_max_right _ _)
      rw [mul_comm]
      exact SchwartzMap.norm_pow_mul_le_seminorm ℂ φ k _
  | zero =>
    exact ⟨continuous_const, ⟨0, fun _ _ => rfl⟩, fun _ => ⟨0, fun _ => by simp⟩⟩
  | add f g _ _ hf hg =>
    obtain ⟨hfc, ⟨R, hR⟩, hf⟩ := hf
    obtain ⟨hgc, ⟨T, hT⟩, hg⟩ := hg
    refine ⟨hfc.add hgc, ⟨fun v => max (R v) (T v), ?_⟩, ?_⟩
    · intro x hx
      have hfz := hR x (fun h => hx (fun v => (h v).trans (le_max_left _ _)))
      have hgz := hT x (fun h => hx (fun v => (h v).trans (le_max_right _ _)))
      change f x + g x = 0
      rw [hfz, hgz, add_zero]
    · intro k
      obtain ⟨B, hB⟩ := hf k
      obtain ⟨C, hC⟩ := hg k
      refine ⟨B + C, fun x => ?_⟩
      change ‖f x + g x‖ * ‖x.1 w‖ ^ k ≤ _
      calc
        _ ≤ (‖f x‖ + ‖g x‖) * ‖x.1 w‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
        _ ≤ _ := by rw [add_mul]; exact add_le_add (hB x) (hC x)
  | smul c f _ hf =>
    obtain ⟨hfc, ⟨R, hR⟩, hf⟩ := hf
    refine ⟨hfc.const_smul c, ⟨R, fun x hx => ?_⟩, ?_⟩
    · change c * f x = 0
      rw [hR x hx, mul_zero]
    · intro k
      obtain ⟨B, hB⟩ := hf k
      refine ⟨‖c‖ * B, fun x => ?_⟩
      change ‖c * f x‖ * ‖x.1 w‖ ^ k ≤ _
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)

/-- Rational S-local theta on a representative. -/
def rationalSLocalThetaOnIdeles (f : A → ℂ) (g : Aˣ) : ℂ :=
  ∑' u : U, f (unitAtS u * g).val

private theorem rationalSLocalTheta_invariant (f : A → ℂ) (g : Aˣ) (z : U) :
    rationalSLocalThetaOnIdeles S f (unitAtS z * g) =
      rationalSLocalThetaOnIdeles S f g := by
  unfold rationalSLocalThetaOnIdeles
  simp_rw [← mul_assoc, ← map_mul]
  exact (Equiv.mulRight z).tsum_eq (fun u => f (unitAtS u * g).val)

/-- The S-local theta function on the quotient by the actual diagonal S-units. -/
def rationalSLocalTheta (f : A → ℂ) : SIdeleQuotient ℚ S → ℂ :=
  Quotient.lift (rationalSLocalThetaOnIdeles S f) (fun g k h => by
    have hx : k / g ∈ sUnitImage ℚ S :=
      (QuotientGroup.eq_one_iff (k / g)).mp (by
        change QuotientGroup.mk' (sUnitImage ℚ S) (k / g) = 1
        rw [map_div]
        exact div_eq_one.mpr (Quotient.sound h).symm)
    obtain ⟨u, hu⟩ := hx
    have he : unitAtS u * g = k := by
      change unitAtS u = k / g at hu
      rw [hu, div_mul_cancel]
    rw [← he, rationalSLocalTheta_invariant])

@[simp] theorem rationalSLocalTheta_mk (f : A → ℂ) (g : Aˣ) :
    rationalSLocalTheta S f (QuotientGroup.mk g) = rationalSLocalThetaOnIdeles S f g := rfl


private theorem rationalNorm_pos (g : Aˣ) : 0 < ratNorm g :=
  ideleNorm_pos ℚ (sLocalEmbed ℚ S g).val

private theorem rationalNorm_continuous : Continuous (ratNorm : Aˣ → ℝ) := by
  rw [show (ratNorm : Aˣ → ℝ) =
    (fun g : Aˣ => ‖g.val.1 w‖ * ∏ v : S, ‖g.val.2 v‖) from funext (rat_sIdeleNorm_eq S)]
  exact (by fun_prop : Continuous (fun g : Aˣ => ‖g.val.1 w‖)).mul
    (continuous_finsetProd _ (fun _ _ => by fun_prop))

private theorem rationalFiniteNorm_eventually (g : Aˣ) :
    ∀ᶠ a : Aˣ in 𝓝 g, ∀ v : S, ‖a.val.2 v‖ = ‖g.val.2 v‖ := by
  apply Filter.eventually_all.2
  intro v
  have hn := norm_pos_iff.mpr (rat_sIdele_finite_ne_zero S g v)
  have hc : Continuous (fun a : Aˣ => a.val.2 v) := by fun_prop
  filter_upwards [hc.continuousAt (Metric.ball_mem_nhds _ hn)] with a ha
  have hdist : dist (a.val.2 v) (g.val.2 v) < dist (g.val.2 v) 0 := by
    change dist (a.val.2 v) (g.val.2 v) < ‖g.val.2 v‖ at ha
    simpa only [dist_zero_right] using ha
  have h := IsUltrametricDist.dist_eq_max_of_dist_ne_dist _ _ 0 hdist.ne
  rw [max_eq_right hdist.le] at h
  simpa only [dist_zero_right] using h

private theorem rationalSLocalTheta_localMajorant {f : A → ℂ} (R : S → ℝ)
    (hR : ∀ x, (¬ ∀ v, ‖x.2 v‖ ≤ R v) → f x = 0)
    (B₀ B₂ : ℝ) (h₀ : ∀ x, ‖f x‖ ≤ B₀) (h₂ : ∀ x, ‖f x‖ * ‖x.1 w‖ ^ 2 ≤ B₂)
    (g : Aˣ) : ∃ V ∈ 𝓝 g, ∃ u : U → ℝ, Summable u ∧
      ∀ z a, a ∈ V → ‖f (unitAtS z * a).val‖ ≤ u z := by
  let e : Fin S.card ≃ S := S.equivFin.symm
  let q : Fin S.card → ℝ := fun i => (e i).val.asIdeal.absNorm
  have hq (i : Fin S.card) : 1 < q i :=
    Nat.one_lt_cast.mpr (HeightOneSpectrum.one_lt_absNorm (e i).val)
  obtain ⟨Q, hQ, hgrid⟩ := rat_sUnit_grid S R e
  let D := max 1 (max B₀ (B₂ * Q ^ 2))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  let φ (t : ℝ) : ℂ := (D * ((max 1 t) ^ 2)⁻¹ : ℝ)
  have hφ (t : ℝ) : ‖φ t‖ = D * ((max 1 t) ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  obtain ⟨T, C, hT, _, hs⟩ := rationalSamplingWithEmpty S.card q hq φ D hD
    (fun t _ => by
      rw [hφ]
      have hp : 1 ≤ (max 1 t) ^ 2 := one_le_pow₀ (le_max_left _ _)
      exact mul_le_of_le_one_right hD.le ((inv_le_one₀ (zero_lt_one.trans_le hp)).mpr hp))
    (fun t ht => by rw [hφ, max_eq_right ht, div_eq_mul_inv])
  let t := min (T / 2) (ratNorm g / 2)
  have hTg := rationalNorm_pos S g
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htT : t < T := (min_le_left _ _).trans_lt (by linarith)
  have htg : t < ratNorm g := (min_le_right _ _).trans_lt (by linarith)
  let V := {a : Aˣ | t < ratNorm a ∧ ∀ v : S, ‖a.val.2 v‖ = ‖g.val.2 v‖}
  have hlow : ∀ᶠ a : Aˣ in 𝓝 g, t < ratNorm a :=
    (rationalNorm_continuous S).continuousAt (Ioi_mem_nhds htg)
  have hV : V ∈ 𝓝 g := hlow.and (rationalFiniteNorm_eventually S g)
  let P : Set U := {z | ∀ v, ‖(unitAtS z * g).val.2 v‖ ≤ R v}
  obtain ⟨index, hindex⟩ := hgrid g
  let majorant (k : Fin S.card → ℕ) := ‖φ ((∏ i, q i ^ k i) * t)‖
  let uP (z : P) := majorant (index z).2
  have hsum : Summable majorant := (hs t ht htT).1
  have hB : Summable (fun p : Bool × (Fin S.card → ℕ) => majorant p.2) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨fun _ => hsum, Summable.of_finite⟩
  have huP : Summable uP := hB.comp_injective index.injective
  let u (z : U) := if hz : z ∈ P then uP ⟨z, hz⟩ else 0
  have hu : Summable u := by
    have he (z : U) : P.indicator u z = u z := by
      by_cases hz : z ∈ P <;> simp [u, hz]
    have hsU : Summable (u ∘ Subtype.val : P → ℝ) := huP.congr (fun z => by
      change uP z = u z.val
      rw [show u z.val = uP z from dite_eq_left z.property])
    exact ((summable_subtype_iff_indicator (s := P) (f := u)).mp hsU).congr he
  refine ⟨V, hV, u, hu, fun z a ha => ?_⟩
  have hcoord (v : S) : ‖(unitAtS z * a).val.2 v‖ = ‖(unitAtS z * g).val.2 v‖ := by
    change ‖(unitAtS z).val.2 v * a.val.2 v‖ = ‖(unitAtS z).val.2 v * g.val.2 v‖
    rw [norm_mul, norm_mul, ha.2 v]
  by_cases hz : z ∈ P
  · let k := (index ⟨z, hz⟩).2
    let L := ∏ i, q i ^ k i
    have hL : 0 < L := Finset.prod_pos fun i _ => pow_pos (zero_lt_one.trans (hq i)) _
    have he : ‖(unitAtS z * a).val.1 w‖ * Q = L * ratNorm a := by
      have hg' := hindex ⟨z, hz⟩
      have hnorm := rat_sIdeleNorm_eq S (unitAtS z * g)
      have hanorm := rat_sIdeleNorm_eq S (unitAtS z * a)
      rw [rat_sIdeleNorm_unit_mul] at hnorm hanorm
      simp_rw [hcoord] at hanorm
      let ev : A →+* Rat.infinitePlace.Completion :=
        (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
      have hne : ‖(unitAtS z * g).val.1 w‖ ≠ 0 :=
        norm_ne_zero_iff.mpr ((unitAtS z * g).isUnit.map ev).ne_zero
      have hLQ : Q = L * ∏ v : S, ‖(unitAtS z * g).val.2 v‖ := by
        apply mul_left_cancel₀ hne
        calc
          _ = L * ratNorm g := hg'
          _ = _ := by rw [hnorm]; ac_rfl
      rw [hLQ, hanorm]
      ac_rfl
    have hmain : ‖f (unitAtS z * a).val‖ ≤ ‖φ (L * ratNorm a)‖ := by
      rw [hφ, ← he]
      let x := (unitAtS z * a).val
      change ‖f x‖ ≤ D * ((max 1 (‖x.1 w‖ * Q)) ^ 2)⁻¹
      rcases le_total (‖x.1 w‖ * Q) 1 with hx | hx
      · rw [max_eq_left hx, one_pow, inv_one, mul_one]
        exact (h₀ x).trans ((le_max_left _ _).trans (le_max_right _ _))
      · rw [max_eq_right hx, ← div_eq_mul_inv]
        apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hx) _)).mpr
        rw [mul_pow, ← mul_assoc]
        exact (mul_le_mul_of_nonneg_right (h₂ x) (sq_nonneg Q)).trans
          ((le_max_right _ _).trans (le_max_right _ _))
    refine hmain.trans ?_
    change ‖φ (L * ratNorm a)‖ ≤ u z
    rw [show u z = ‖φ (L * t)‖ by simp [u, hz, uP, majorant, L, k], hφ, hφ]
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
      (max_le_max_left _ (mul_le_mul_of_nonneg_left ha.1.le hL.le)) _
  · have hcut : ¬ ∀ v, ‖(unitAtS z * a).val.2 v‖ ≤ R v := by
      simpa only [hcoord, P, mem_ofPred_eq] using hz
    rw [hR _ hcut, norm_zero]
    simp [u, hz]

/-- The S-local sum is absolutely convergent at every idele and locally
uniform in the idele, so it descends to a continuous theta function. -/
theorem rationalSLocalTheta_continuous {f : A → ℂ} (hf : f ∈ rationalSLocalTestFunctions S) :
    Continuous (rationalSLocalTheta S f) := by
  obtain ⟨hc, ⟨R, hR⟩, hb⟩ := rationalSLocalTest_bounds S hf
  obtain ⟨B₀, h₀⟩ := hb 0
  obtain ⟨B₂, h₂⟩ := hb 2
  simp only [pow_zero, mul_one] at h₀
  apply (QuotientGroup.isQuotientMap_mk (sUnitImage ℚ S)).continuous_iff.mpr
  change Continuous (rationalSLocalThetaOnIdeles S f)
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨V, hV, u, hu, hbound⟩ := rationalSLocalTheta_localMajorant S R hR B₀ B₂ h₀ h₂ g
  let term (z : U) (a : Aˣ) := f (unitAtS z * a).val
  have hs := HasSumUniformlyOn.of_norm_le_summable hu (f := term) hbound
  have hl := hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hs
  have hcont (z : U) : Continuous (term z) := hc.comp (by fun_prop)
  apply (hl.continuousOn (Frequently.of_forall fun s => (continuous_finsetSum _ (fun z _ => hcont z)).continuousOn)
    g (mem_of_mem_nhds hV)).continuousAt hV


/-- The absolute S-unit orbit sum is convergent at every S-idele. -/
theorem rationalSLocalTheta_absoluteSummable {f : A → ℂ}
    (hf : f ∈ rationalSLocalTestFunctions S) (g : Aˣ) :
    Summable (fun z : U => ‖f (unitAtS z * g).val‖) := by
  obtain ⟨_, ⟨R, hR⟩, hb⟩ := rationalSLocalTest_bounds S hf
  obtain ⟨B₀, h₀⟩ := hb 0
  obtain ⟨B₂, h₂⟩ := hb 2
  simp only [pow_zero, mul_one] at h₀
  obtain ⟨V, hV, u, hu, hbound⟩ := rationalSLocalTheta_localMajorant S R hR B₀ B₂ h₀ h₂ g
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => hbound z g (mem_of_mem_nhds hV))

def rationalSLocalNormOnClasses (a : SIdeleQuotient ℚ S) : ℝ :=
  ((sQuotientNorm ℚ S a).val : ℝ)

@[simp] private theorem rationalSLocalNormOnClasses_mk (a : Aˣ) :
    rationalSLocalNormOnClasses S (QuotientGroup.mk a) = ratNorm a := rfl

private theorem rationalSLocalNormOnClasses_mul (a b : SIdeleQuotient ℚ S) :
    rationalSLocalNormOnClasses S (a * b) =
      rationalSLocalNormOnClasses S a * rationalSLocalNormOnClasses S b := by
  unfold rationalSLocalNormOnClasses
  rw [map_mul]
  rfl

/-- Logarithmic growth of rational S-local theta, including the case with
no finite places in S. -/
theorem rationalSLocalTheta_logGrowth {f : A → ℂ} (hf : f ∈ rationalSLocalTestFunctions S) :
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧
      ∀ a : SIdeleQuotient ℚ S, rationalSLocalNormOnClasses S a < T →
        ‖rationalSLocalTheta S f a‖ ≤
          C * |Real.log (rationalSLocalNormOnClasses S a)| ^ S.card := by
  obtain ⟨_, ⟨R, hR⟩, hb⟩ := rationalSLocalTest_bounds S hf
  obtain ⟨B₀, h₀⟩ := hb 0
  obtain ⟨B₂, h₂⟩ := hb 2
  simp only [pow_zero, mul_one] at h₀
  obtain ⟨T, C, hT, hC, hb⟩ := rat_sUnit_sum_norm_log_growth S f R B₀ B₂ hR h₀ h₂
  refine ⟨T, C, hT, hC, fun a ha => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  rw [rationalSLocalNormOnClasses_mk] at ha
  rw [rationalSLocalNormOnClasses_mk, rationalSLocalTheta_mk, rationalSLocalThetaOnIdeles]
  exact (norm_tsum_le_tsum_norm (rationalSLocalTheta_absoluteSummable S hf g)).trans (hb g ha)

/-- The compact norm-one subgroup of the rational S-idele classes. -/
abbrev RationalSLocalNormOne := (sQuotientNorm ℚ S).ker

theorem rationalSLocalNormOne_compact : CompactSpace (RationalSLocalNormOne S) := by
  apply isCompact_iff_compactSpace.mp
  exact (sQuotientNorm_proper ℚ S).isCompact_preimage isCompact_singleton

section Homogeneous

variable [MeasurableSpace (RationalSLocalNormOne S)] [BorelSpace (RationalSLocalNormOne S)]

/-- The homogeneous theta function is the compact character average over
the norm-one subgroup of the actual S-idele classes. -/
def rationalSLocalHomogeneousTheta (μ : Measure (RationalSLocalNormOne S))
    (ω : PontryaginDual (RationalSLocalNormOne S)) (f : A → ℂ)
    (a : SIdeleQuotient ℚ S) : ℂ :=
  ∫ k, ((ω k : Circle) : ℂ) * rationalSLocalTheta S f (k.val * a) ∂μ

theorem rationalSLocalHomogeneousTheta_integrable (μ : Measure (RationalSLocalNormOne S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (RationalSLocalNormOne S))
    {f : A → ℂ} (hf : f ∈ rationalSLocalTestFunctions S) (a : SIdeleQuotient ℚ S) :
    Integrable (fun k => ((ω k : Circle) : ℂ) * rationalSLocalTheta S f (k.val * a)) μ := by
  letI : CompactSpace (RationalSLocalNormOne S) := rationalSLocalNormOne_compact S
  have hw := continuous_subtype_val.comp ω.continuous
  have hk : Continuous (fun k : RationalSLocalNormOne S => k.val * a) :=
    continuous_subtype_val.mul (continuous_const (y := a))
  have h := hw.mul ((rationalSLocalTheta_continuous S hf).comp hk)
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [BorelSpace (RationalSLocalNormOne S)] in
/-- The same logarithmic bound holds for every compact-character average. -/
theorem rationalSLocalHomogeneousTheta_logGrowth (μ : Measure (RationalSLocalNormOne S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (RationalSLocalNormOne S))
    {f : A → ℂ} (hf : f ∈ rationalSLocalTestFunctions S) :
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧
      ∀ a : SIdeleQuotient ℚ S, rationalSLocalNormOnClasses S a < T →
        ‖rationalSLocalHomogeneousTheta S μ ω f a‖ ≤
          C * |Real.log (rationalSLocalNormOnClasses S a)| ^ S.card := by
  letI : CompactSpace (RationalSLocalNormOne S) := rationalSLocalNormOne_compact S
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨T, C, hT, hC, h⟩ := rationalSLocalTheta_logGrowth S hf
  let M : ℝ := (μ univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨T, C * (M + 1), hT, mul_pos hC (by positivity), fun a ha => ?_⟩
  let B := |Real.log (rationalSLocalNormOnClasses S a)| ^ S.card
  have hB : 0 ≤ B := pow_nonneg (abs_nonneg _) _
  have hpoint (k : RationalSLocalNormOne S) :
      ‖((ω k : Circle) : ℂ) * rationalSLocalTheta S f (k.val * a)‖ ≤ C * B := by
    have hk : rationalSLocalNormOnClasses S k.val = 1 := by
      unfold rationalSLocalNormOnClasses
      rw [show sQuotientNorm ℚ S k.val = 1 from k.property]
      rfl
    have hm : rationalSLocalNormOnClasses S (k.val * a) =
      rationalSLocalNormOnClasses S a := by rw [rationalSLocalNormOnClasses_mul, hk, one_mul]
    rw [norm_mul, Circle.norm_coe, one_mul]
    simpa only [hm, B] using h (k.val * a) (by rwa [hm])
  unfold rationalSLocalHomogeneousTheta
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hpoint)).trans ?_
  change C * B * M ≤ C * (M + 1) * B
  rw [mul_right_comm C B M, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hB) hC.le

end Homogeneous


end
end Masullo
