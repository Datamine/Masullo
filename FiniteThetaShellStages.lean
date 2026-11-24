import FinitePrincipalValue
import SUnitRank
import Mathlib.Topology.Algebra.IsOpenUnits

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

section Shells

variable {K : Type*} [NormedField K]

private abbrev Test := locallyConstantTests K

private def mulTest (f g : Test (K := K)) : Test (K := K) :=
  ⟨f.val * g.val, f.property.1.mul g.property.1, f.property.2.mul_right⟩

variable (p : Kˣ) (hc : IsCompact (Metric.closedBall (0 : K) 1))
  (ho : IsOpen (Metric.closedBall (0 : K) 1))

/-- The indicator of the unit ball, pulled back by inverse multiplication
by a power of the chosen dilation. -/
def thetaBallTest (n : ℤ) : Test (K := K) :=
  locallyConstantTestTranslate K (p ^ n) (compactOpenIndicator K ⟨_, hc, ho⟩)

theorem thetaBallTest_apply (n : ℤ) (x : K) :
    (thetaBallTest p hc ho n).val x = if ‖x‖ ≤ ‖p.val‖ ^ n then 1 else 0 := by
  change (Metric.closedBall (0 : K) 1).indicator (fun _ => (1 : ℂ))
    ((↑((p ^ n)⁻¹) : K) * x) = _
  rw [indicator_apply, Metric.mem_closedBall, dist_zero_right, norm_mul,
    Units.val_inv_eq_inv_val, norm_inv, Units.val_zpow_eq_zpow_val, norm_zpow,
    inv_mul_le_iff₀ (zpow_pos (norm_pos_iff.mpr p.ne_zero) _), mul_one]

private def thetaCut (n : ℤ) (f : Test (K := K)) : Test (K := K) :=
  mulTest f (thetaBallTest p hc ho n)

private theorem thetaCut_apply (n : ℤ) (f : Test (K := K)) (x : K) :
    (thetaCut p hc ho n f).val x = if ‖x‖ ≤ ‖p.val‖ ^ n then f.val x else 0 := by
  change f.val x * (thetaBallTest p hc ho n).val x = _
  rw [thetaBallTest_apply]
  split_ifs <;> simp

/-- The annulus used as the common support for normalized shell tests. -/
def thetaBaseAnnulus : Set K := {x | ‖p.val‖ < ‖x‖ ∧ ‖x‖ ≤ 1}

/-- Cut a test down to the common annulus between the unit ball and its
dilate by the chosen contracting unit. -/
def thetaAnnulusTest (f : Test (K := K)) : Test (K := K) :=
  thetaCut p hc ho 0 f - thetaCut p hc ho 1 f

theorem thetaAnnulusTest_apply (hp : ‖p.val‖ < 1) (f : Test (K := K)) (x : K) :
    (thetaAnnulusTest p hc ho f).val x =
      if x ∈ thetaBaseAnnulus p then f.val x else 0 := by
  change (thetaCut p hc ho 0 f).val x - (thetaCut p hc ho 1 f).val x = _
  rw [thetaCut_apply, thetaCut_apply, zpow_zero, zpow_one]
  by_cases h₁ : ‖x‖ ≤ 1 <;> by_cases h₂ : ‖x‖ ≤ ‖p.val‖
  · simp [thetaBaseAnnulus, h₁, h₂, h₂.not_gt]
  · simp [thetaBaseAnnulus, h₁, h₂, lt_of_not_ge h₂]
  · exact (h₁ (h₂.trans hp.le)).elim
  · simp [thetaBaseAnnulus, h₁, h₂]

variable (hp : ‖p.val‖ < 1)
include hp

private theorem thetaCut_sub (n : ℤ) (f : Test (K := K)) :
    thetaCut p hc ho n f - thetaCut p hc ho (n+1) f =
      locallyConstantTestTranslate K (p ^ n)
        (thetaAnnulusTest p hc ho (locallyConstantTestTranslate K (p ^ (-n)) f)) := by
  apply Subtype.ext
  funext x
  change (thetaCut p hc ho n f).val x - (thetaCut p hc ho (n+1) f).val x =
    (thetaAnnulusTest p hc ho (locallyConstantTestTranslate K (p ^ (-n)) f)).val
      ((↑((p ^ n)⁻¹) : K) * x)
  have hr : 0 < ‖p.val‖ ^ n := zpow_pos (norm_pos_iff.mpr p.ne_zero) n
  have hnorm : ‖(↑((p ^ n)⁻¹) : K) * x‖ = (‖p.val‖ ^ n)⁻¹ * ‖x‖ := by
    rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, Units.val_zpow_eq_zpow_val, norm_zpow]
  have hAnn : (↑((p ^ n)⁻¹) : K) * x ∈ thetaBaseAnnulus p ↔
      ‖p.val‖ ^ (n+1) < ‖x‖ ∧ ‖x‖ ≤ ‖p.val‖ ^ n := by
    change _ < ‖(↑((p ^ n)⁻¹) : K) * x‖ ∧ ‖(↑((p ^ n)⁻¹) : K) * x‖ ≤ 1 ↔ _
    rw [hnorm, lt_inv_mul_iff₀ hr, inv_mul_le_iff₀ hr, mul_one,
      ← zpow_add_one₀ (norm_pos_iff.mpr p.ne_zero).ne']
  have he : (locallyConstantTestTranslate K (p ^ (-n)) f).val ((↑((p ^ n)⁻¹) : K) * x) =
      f.val x := by
    change f.val ((↑((p ^ (-n))⁻¹) : K) * ((↑((p ^ n)⁻¹) : K) * x)) = _
    rw [zpow_neg, inv_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [thetaCut_apply, thetaCut_apply, thetaAnnulusTest_apply p hc ho hp, hAnn, he]
  have hh : ‖p.val‖ ^ (n+1) ≤ ‖p.val‖ ^ n :=
    (zpow_le_zpow_iff_right_of_lt_one₀ (norm_pos_iff.mpr p.ne_zero) hp).mpr (by omega)
  by_cases h₁ : ‖x‖ ≤ ‖p.val‖ ^ n <;> by_cases h₂ : ‖x‖ ≤ ‖p.val‖ ^ (n+1)
  · simp [h₁, h₂, h₂.not_gt]
  · simp [h₁, h₂, lt_of_not_ge h₂]
  · exact (h₁ (h₂.trans hh)).elim
  · simp [h₁, h₂]

private theorem thetaCut_outer (f : Test (K := K)) :
    ∃ M : ℕ, thetaCut p hc ho (-(M : ℤ)) f = f := by
  have hr := norm_pos_iff.mpr p.ne_zero
  obtain ⟨R, hR⟩ := f.property.2.isBounded.subset_closedBall (0 : K)
  have ht := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hr).mpr hp)
  obtain ⟨M, hM⟩ := (ht.eventually (eventually_gt_atTop R)).exists
  refine ⟨M, Subtype.ext (funext fun x ↦ ?_)⟩
  rw [thetaCut_apply]
  by_cases hx : ‖x‖ ≤ ‖p.val‖ ^ (-(M : ℤ))
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx]
    symm
    apply image_eq_zero_of_notMem_tsupport
    intro he
    apply hx
    change ‖p.val‖⁻¹ ^ M > R at hM
    have hm := hR he
    rw [Metric.mem_closedBall, dist_zero_right] at hm
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hm.trans hM.le

private theorem thetaCut_inner (f : Test (K := K)) :
    ∃ N : ℕ, thetaCut p hc ho N f = f.val 0 • thetaBallTest p hc ho N := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (f.property.1.eventually_eq 0)
  have hT := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg p.val) hp
  obtain ⟨N, hN⟩ := (hT.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, Subtype.ext (funext fun x ↦ ?_)⟩
  change (thetaCut p hc ho N f).val x = f.val 0 * (thetaBallTest p hc ho N).val x
  rw [thetaCut_apply, thetaBallTest_apply]
  by_cases hx : ‖x‖ ≤ ‖p.val‖ ^ (N : ℤ)
  · have hxe : f.val x = f.val 0 := hb (by
      rw [Metric.mem_ball, dist_zero_right]
      rw [zpow_natCast] at hx
      exact hx.trans_lt hN)
    rw [ite_eq_left hx, ite_eq_left hx, mul_one, hxe]
  · rw [ite_eq_right hx, ite_eq_right hx, mul_zero]

/-- A compactly supported locally constant test is a finite sum of dilates
of tests on the same compact annulus, together with a dilated ball term. -/
theorem thetaShell_normalForm (f : Test (K := K)) :
    ∃ M N : ℕ, f = f.val 0 • thetaBallTest p hc ho N +
      ∑ i ∈ Finset.range (M + N),
        locallyConstantTestTranslate K (p ^ (-(M : ℤ) + (i : ℤ)))
          (thetaAnnulusTest p hc ho
            (locallyConstantTestTranslate K (p ^ (-(-(M : ℤ) + (i : ℤ)))) f)) := by
  obtain ⟨M, hM⟩ := thetaCut_outer p hc ho hp f
  obtain ⟨N, hN⟩ := thetaCut_inner p hc ho hp f
  let a (i : ℕ) := thetaCut p hc ho (-(M : ℤ) + (i : ℤ)) f
  have hs (L : ℕ) : (∑ i ∈ Finset.range L, (a i - a (i+1))) = a 0 - a L := by
    induction L with
    | zero => simp
    | succ L ih => rw [Finset.sum_range_succ, ih]; abel
  have he (i : ℕ) : (-(M : ℤ) + (i : ℤ) + 1) = -(M : ℤ) + ((i + 1 : ℕ) : ℤ) := by omega
  have hsum :
      (∑ i ∈ Finset.range (M + N),
        locallyConstantTestTranslate K (p ^ (-(M : ℤ) + (i : ℤ)))
          (thetaAnnulusTest p hc ho
            (locallyConstantTestTranslate K (p ^ (-(-(M : ℤ) + (i : ℤ)))) f))) =
        ∑ i ∈ Finset.range (M + N), (a i - a (i+1)) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← thetaCut_sub p hc ho hp, he i]
  have h₀ : a 0 = f := by simpa [a] using hM
  have h₁ : a (M+N) = f.val 0 • thetaBallTest p hc ho N := by simpa [a] using hN
  refine ⟨M, N, ?_⟩
  rw [hsum, hs, h₀, h₁]
  abel

include hc ho in

omit hp in
private theorem thetaBaseAnnulus_compact : IsCompact (thetaBaseAnnulus p) := by
  let B := {x : K | ‖x‖ ≤ ‖p.val‖}
  have he : B = {x | (thetaBallTest p hc ho 1).val x = 1} := by
    ext x
    simp [B, thetaBallTest_apply]
  have hB : IsOpen B := he ▸ (thetaBallTest p hc ho 1).property.1.isOpen_fiber 1
  have heq : thetaBaseAnnulus p = Metric.closedBall (0 : K) 1 \ B := by
    ext x
    simp only [thetaBaseAnnulus, mem_ofPred_eq, Set.mem_sdiff, Metric.mem_closedBall,
      dist_zero_right, B, not_le]
    exact and_comm
  exact heq ▸ hc.diff hB

/-- Locally constant tests on the normalized annulus which are invariant under
a fixed group of integral units. -/
def thetaAnnulusInvariant (H : Subgroup Kˣ) : Submodule ℂ (Test (K := K)) where
  carrier := {f | (∀ x, x ∉ thetaBaseAnnulus p → f.val x = 0) ∧
    ∀ u : H, ∀ x : K, f.val (u.val.val * x) = f.val x}
  zero_mem' := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  add_mem' hf hg := by
    refine ⟨fun x hx ↦ ?_, fun u x ↦ ?_⟩
    · simp only [Submodule.coe_add, Pi.add_apply]
      rw [hf.1 x hx, hg.1 x hx, add_zero]
    · simp only [Submodule.coe_add, Pi.add_apply]
      rw [hf.2 u x, hg.2 u x]
  smul_mem' c _ hf := by
    refine ⟨fun x hx ↦ ?_, fun u x ↦ ?_⟩
    · change c * _ = 0
      rw [hf.1 x hx, mul_zero]
    · change c * _ = c * _
      rw [hf.2 u x]

include hc ho in
omit hp in
/-- The normalized annulus has only finitely many orbits under an open subgroup
of the local units. Evaluation on one point per orbit makes its invariant test
space finite-dimensional. -/
theorem thetaAnnulusInvariant_finiteDimensional (H : Subgroup Kˣ)
    (hH : IsOpen (H : Set Kˣ)) :
    FiniteDimensional ℂ (thetaAnnulusInvariant p H) := by
  let U (a : Kˣ) : Set K := Units.val '' ((fun h : Kˣ ↦ h * a) '' (H : Set Kˣ))
  have hopen (a : Kˣ) : IsOpen (U a) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _
      ((Homeomorph.mulRight a).isOpenMap _ hH)
  have hcover : thetaBaseAnnulus p ⊆ ⋃ a : Kˣ, U a := by
    intro x hx
    have hn : x ≠ 0 := by
      intro he
      exact (norm_nonneg p.val).not_gt (by simpa [he] using hx.1)
    let a := Units.mk0 x hn
    exact mem_iUnion.mpr ⟨a, a, ⟨1, H.one_mem, one_mul _⟩, rfl⟩
  obtain ⟨s, hs⟩ := (thetaBaseAnnulus_compact p hc ho).elim_finite_subcover U hopen hcover
  let L : thetaAnnulusInvariant p H →ₗ[ℂ] (s → ℂ) :=
    LinearMap.pi fun a ↦ (LinearMap.proj a.val.val).comp
      ((Test (K := K)).subtype.comp (thetaAnnulusInvariant p H).subtype)
  letI : FiniteDimensional ℂ (s → ℂ) := by infer_instance
  refine FiniteDimensional.of_injective L ?_
  intro f g hfg
  apply Subtype.ext
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ thetaBaseAnnulus p
  · obtain ⟨a, ha⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨ha', hax⟩ := mem_iUnion.mp ha
    obtain ⟨b, ⟨u, hu, rfl⟩, rfl⟩ := hax
    have he : f.val.val a.val = g.val.val a.val := congrFun hfg ⟨a, ha'⟩
    change f.val.val (u.val * a.val) = g.val.val (u.val * a.val)
    rw [f.property.2 ⟨u, hu⟩ a.val, g.property.2 ⟨u, hu⟩ a.val, he]
  · rw [f.property.1 x hx, g.property.1 x hx]

/-- Each normalized annulus term is supported on the common annulus and
retains invariance under the chosen integral units. -/
theorem thetaAnnulus_translate_mem_invariants (H : Subgroup Kˣ)
    (hnorm : ∀ u : H, ‖u.val.val‖ = 1) (f : Test (K := K))
    (hf : ∀ u : H, ∀ x : K, f.val (u.val.val * x) = f.val x) (a : Kˣ) :
    thetaAnnulusTest p hc ho (locallyConstantTestTranslate K a f) ∈
      thetaAnnulusInvariant p H := by
  refine ⟨fun x hx ↦ ?_, fun u x ↦ ?_⟩
  · rw [thetaAnnulusTest_apply p hc ho hp, ite_eq_right hx]
  · rw [thetaAnnulusTest_apply p hc ho hp, thetaAnnulusTest_apply p hc ho hp]
    have he : u.val.val * x ∈ thetaBaseAnnulus p ↔ x ∈ thetaBaseAnnulus p := by
      change ‖p.val‖ < ‖u.val.val * x‖ ∧ ‖u.val.val * x‖ ≤ 1 ↔ _
      rw [norm_mul, hnorm u, one_mul]
      rfl
    have htr : (locallyConstantTestTranslate K a f).val (u.val.val * x) =
        (locallyConstantTestTranslate K a f).val x := by
      change f.val (a.inv * (u.val.val * x)) = f.val (a.inv * x)
      rw [mul_left_comm, hf]
    simp only [he, htr]

/-- For tests invariant under a fixed open subgroup of integral units, the
normalized shell terms all lie in one finite-dimensional test space. -/
theorem thetaShell_invariant_normalForm (H : Subgroup Kˣ)
    (hH : IsOpen (H : Set Kˣ)) (hnorm : ∀ u : H, ‖u.val.val‖ = 1)
    (f : Test (K := K)) (hf : ∀ u : H, ∀ x : K, f.val (u.val.val * x) = f.val x) :
    FiniteDimensional ℂ (thetaAnnulusInvariant p H) ∧
      ∃ (M N : ℕ) (g : ℕ → thetaAnnulusInvariant p H),
        f = f.val 0 • locallyConstantTestTranslate K (p ^ (N : ℤ))
            (compactOpenIndicator K ⟨_, hc, ho⟩) +
          ∑ i ∈ Finset.range (M + N),
            locallyConstantTestTranslate K (p ^ (-(M : ℤ) + (i : ℤ))) (g i).val := by
  refine ⟨thetaAnnulusInvariant_finiteDimensional p hc ho H hH, ?_⟩
  obtain ⟨M, N, h⟩ := thetaShell_normalForm p hc ho hp f
  let g (i : ℕ) : thetaAnnulusInvariant p H :=
    ⟨thetaAnnulusTest p hc ho
        (locallyConstantTestTranslate K (p ^ (-(-(M : ℤ) + (i : ℤ)))) f),
      thetaAnnulus_translate_mem_invariants p hc ho hp H hnorm f hf _⟩
  exact ⟨M, N, g, h⟩

omit hp in
/-- A norm-one dilation preserves the normalized annulus subspace, even if
the dilating unit lies outside the open subgroup used for invariance. -/
theorem thetaAnnulusInvariant_translate_mem (H : Subgroup Kˣ)
    (a : Kˣ) (ha : ‖a.val‖ = 1) {f : Test (K := K)} (hf : f ∈ thetaAnnulusInvariant p H) :
    locallyConstantTestTranslate K a f ∈ thetaAnnulusInvariant p H := by
  refine ⟨fun x hx ↦ ?_, fun u x ↦ ?_⟩
  · change f.val (a.inv * x) = 0
    apply hf.1
    change ¬ (‖p.val‖ < ‖a.inv * x‖ ∧ ‖a.inv * x‖ ≤ 1)
    rw [show a.inv = a.val⁻¹ from Units.val_inv_eq_inv_val a, norm_mul, norm_inv,
      ha, inv_one, one_mul]
    exact hx
  · change f.val (a.inv * (u.val.val * x)) = f.val (a.inv * x)
    rw [mul_left_comm, hf.2 u]

private def integralStabilizer (f : Test (K := K)) : Subgroup Kˣ where
  carrier := {u | ‖u.val‖ = 1 ∧ ∀ x : K, f.val (u.val * x) = f.val x}
  one_mem' := by simp
  mul_mem' {u w} hu hw := by
    refine ⟨?_, fun x ↦ ?_⟩
    · change ‖u.val * w.val‖ = 1
      rw [norm_mul, hu.1, hw.1, one_mul]
    · change f.val ((u.val * w.val) * x) = f.val x
      rw [mul_assoc, hu.2, hw.2]
  inv_mem' {u} hu := by
    refine ⟨?_, fun x ↦ ?_⟩
    · change ‖u.inv‖ = 1
      rw [show u.inv = u.val⁻¹ from Units.val_inv_eq_inv_val u, norm_inv, hu.1, inv_one]
    · have h := hu.2 (u.inv * x)
      rw [← mul_assoc, u.val_inv, one_mul] at h
      exact h.symm

include ho in
omit hp in
private theorem integralStabilizer_open (f : Test (K := K)) :
    IsOpen (integralStabilizer f : Set Kˣ) := by
  let B := Metric.closedBall (0 : K) 1
  have hUnitOpen : IsOpen {u : Kˣ | ‖u.val‖ = 1} := by
    have he : {u : Kˣ | ‖u.val‖ = 1} =
        Units.val ⁻¹' B ∩ (fun u : Kˣ ↦ (u⁻¹).val) ⁻¹' B := by
      ext u
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, B, Metric.mem_closedBall, dist_zero_right,
        Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.mpr u.ne_zero)]
      exact le_antisymm_iff
    rw [he]
    exact (ho.preimage Units.continuous_val).inter (ho.preimage (Units.continuous_val.comp continuous_inv))
  have hF := (locallyConstantTestTranslate_orbit_locallyConstant (G := Kˣ) K f).isOpen_fiber f
  have he : (integralStabilizer f : Set Kˣ) =
      {u : Kˣ | ‖u.val‖ = 1} ∩ {u | locallyConstantTestTranslate K u f = f} := by
    ext u
    change (‖u.val‖ = 1 ∧ ∀ x : K, f.val (u.val * x) = f.val x) ↔
      ‖u.val‖ = 1 ∧ locallyConstantTestTranslate K u f = f
    apply and_congr_right'
    constructor
    · intro h
      apply Subtype.ext
      funext x
      have he := h (u.inv * x)
      rw [← mul_assoc, u.val_inv, one_mul] at he
      exact he.symm
    · intro h x
      have he := congrArg (fun g : Test (K := K) ↦ g.val (u.val * x)) h
      change f.val (u.inv * (u.val * x)) = f.val (u.val * x) at he
      rw [← mul_assoc, u.inv_val, one_mul] at he
      exact he.symm
  rw [he]
  exact hUnitOpen.inter hF

include ho in
omit hp in
/-- Any finite family of local tests has a common open integral-unit
stabilizer. -/
theorem thetaTests_exists_open_integralStabilizer (s : Finset (Test (K := K))) :
    ∃ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) ∧ (∀ u : H, ‖u.val.val‖ = 1) ∧
      (∀ f ∈ s, ∀ u : H, ∀ x : K, f.val (u.val.val * x) = f.val x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨integralStabilizer (0 : Test (K := K)), integralStabilizer_open ho 0, ?_, by simp⟩
    exact fun u ↦ u.property.1
  | insert f s _ ih =>
    obtain ⟨H, hH, hn, hi⟩ := ih
    let A := integralStabilizer f
    refine ⟨A ⊓ H, (integralStabilizer_open ho f).inter hH, fun u ↦ u.property.1.1, ?_⟩
    intro g hg u x
    rcases Finset.mem_insert.mp hg with h | h
    · subst g
      exact u.property.1.2 x
    · exact hi g h ⟨u.val, u.property.2⟩ x

end Shells

section SUnits

open scoped WithZero NNReal

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- At any selected finite place one can use a contracting S-unit, whose
coordinates at every other finite place have norm one. -/
theorem exists_sUnit_contracts_one_place (S : Finset (Place F)) (v : S) :
    ∃ u : (sIntegerRing F S)ˣ,
      ‖(principalIdele F (sUnitToField F S u)).val.2 v.val‖ < 1 ∧
      ∀ w : Place F, w ≠ v.val → ‖(principalIdele F (sUnitToField F S u)).val.2 w‖ = 1 := by
  let H := Nat.card (ClassGroup (𝓞 F))
  have hH : 0 < (H : ℤ) := by exact_mod_cast (Nat.card_pos (α := ClassGroup (𝓞 F)))
  let d (w : S) : ℤ := if w = v then 1 else 0
  obtain ⟨x, hx⟩ := sUnitValuation_classNumber F S d
  let u := x.toMul
  let a := principalIdele F (sUnitToField F S u)
  have hx' (w : S) : ideleOrder F a w.val = (H : ℤ) * d w := by
    have he := congrFun hx w
    change ideleOrder F a w.val = H • d w at he
    simpa only [nsmul_eq_mul] using he
  have hp : ideleOrder F a v.val = (H : ℤ) := by rw [hx' v, show d v = 1 by simp [d], mul_one]
  have hw (w : Place F) (hne : w ≠ v.val) : ideleOrder F a w = 0 := by
    by_cases hs : w ∈ S
    · have hne' : (⟨w, hs⟩ : S) ≠ v := fun h ↦ hne (congrArg Subtype.val h)
      have hd : d ⟨w, hs⟩ = 0 := by simp [d, hne']
      rw [hx' ⟨w, hs⟩, hd, mul_zero]
    · exact (sIdeleBlock_mem_iff F S a).mp (sPrincipal F S u).property w hs
  refine ⟨u, ?_, fun w h ↦ ?_⟩
  · let t := Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom (sUnitToField F S u)
    have hn : (Valued.v (a.val.2 v.val) : WithZero (Multiplicative ℤ)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero t)
    have he := WithZero.exp_log hn
    have hl : WithZero.log (Valued.v (a.val.2 v.val)) < 0 := by
      change -WithZero.log (Valued.v (a.val.2 v.val)) = (H : ℤ) at hp
      omega
    have hv : (Valued.v (a.val.2 v.val) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← he, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact hl
    change ‖a.val.2 v.val‖ < 1
    rw [FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_lt_coe]
    exact (WithZeroMulInt.toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v.val)).mpr hv
  · let t := Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom (sUnitToField F S u)
    change ‖t.val‖ = 1
    exact (finiteCompletion_norm_eq_one_iff F w t).mpr ((ideleOrder_eq_zero_iff F a w).mp (hw w h))

end SUnits

end

end Masullo
