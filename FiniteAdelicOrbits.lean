import AdelicOrbitBoundary
import FinitePrincipalValue
import HeckeEulerProducts

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField RestrictedProduct

noncomputable section

namespace Masullo

private theorem interval_ratio_eq_one {q r u : ℝ} (hq : 1 < q) (hr : r ∈ Ico 1 q)
    (hu : u ∈ Ico 1 q) (n : ℤ) (he : r / u = q ^ n) : r = u := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu.1
  have hr₀ : 0 < r := zero_lt_one.trans_le hr.1
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hl (x : ℝ) (hx : x ∈ Ico 1 q) : 0 ≤ Real.log x ∧ Real.log x < Real.log q :=
    ⟨Real.log_nonneg hx.1, Real.log_lt_log (zero_lt_one.trans_le hx.1) hx.2⟩
  have h := congrArg Real.log he
  rw [Real.log_div hr₀.ne' hu₀.ne', Real.log_zpow] at h
  have h₁ : (-1 : ℝ) < n := by
    by_contra! hn
    have hb := mul_le_mul_of_nonneg_right hn hlogq.le
    linarith [(hl r hr).1, (hl u hu).2]
  have h₂ : (n : ℝ) < 1 := by
    by_contra! hn
    have hb := mul_le_mul_of_nonneg_right hn hlogq.le
    linarith [(hl r hr).2, (hl u hu).1]
  have hn : n = 0 := by
    have lo : -1 < n := by exact_mod_cast h₁
    have hi : n < 1 := by exact_mod_cast h₂
    omega
  simpa [hn, div_eq_one_iff_eq hu₀.ne'] using he

private theorem unit_mul_left_cancel {R : Type*} [Monoid R] (a : Rˣ) {x y : R} :
    a.val * x = a.val * y ↔ x = y := a.isUnit.mul_right_inj

/-- A cyclic modulus lattice gives a half-open fundamental interval and describes
all norm-one transporters as a single coset of the norm-one stabilizer. -/
theorem normOne_orbit_fundamentalInterval {R : Type*} [CommMonoid R]
    (N : Rˣ →* ℝ) (hN : ∀ g, 0 < N g) (z : R) {q : ℝ} (hq : 1 < q)
    (hZ : ∀ r : ℝ, (∃ a : Rˣ, a.val * z = z ∧ N a = r) ↔ ∃ n : ℤ, r = q ^ n)
    (s : Multiplicative ℝ →* Rˣ) (hs : ∀ t, N (s t) = Real.exp t.toAdd)
    (H : Set Rˣ) (hH : ∀ a, a ∈ H ↔ a.val * z = z ∧ N a = 1)
    {x : R} (hx : x ∈ Set.range (fun g : Rˣ ↦ g.val * z)) :
    ∃ (t : Multiplicative ℝ) (a : Rˣ),
      Real.exp t.toAdd ∈ Ico 1 q ∧ N a = 1 ∧ (a⁻¹).val * x = (s t).val * z ∧
      ∀ (u : Multiplicative ℝ) (b : Rˣ), Real.exp u.toAdd ∈ Ico 1 q →
        (N b = 1 ∧ (b⁻¹).val * x = (s u).val * z ↔ u = t ∧ b / a ∈ H) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨n, hn, hlt⟩ := exists_mem_Ico_zpow (hN g) hq
  obtain ⟨k, hk, hkn⟩ := (hZ (q ^ n)).mpr ⟨n, rfl⟩
  let r := N g / q ^ n
  have hqn : 0 < q ^ n := zpow_pos (zero_lt_one.trans hq) _
  have hr : r ∈ Ico 1 q := by
    refine ⟨(le_div_iff₀ hqn).mpr (by simpa using hn), (div_lt_iff₀ hqn).mpr ?_⟩
    simpa [zpow_add_one₀ (zero_lt_one.trans hq).ne', mul_comm] using hlt
  let t := Multiplicative.ofAdd (Real.log r)
  have ht : Real.exp t.toAdd = r := Real.exp_log (zero_lt_one.trans_le hr.1)
  let a := g / (k * s t)
  have ha : N a = 1 := by
    have he : q ^ n * r = N g := by
      dsimp [r]
      field_simp
    rw [show a = g / (k * s t) from rfl, map_div, map_mul, hkn, hs, ht, he,
      div_self (hN g).ne']
  have hmove : (a⁻¹).val * (g.val * z) = (s t).val * z := by
    have heg : g = a * (s t * k) := by simp [a, mul_comm]
    calc
      (a⁻¹).val * (g.val * z) = (a⁻¹ * g).val * z := by rw [Units.val_mul, mul_assoc]
      _ = (s t * k).val * z := by rw [heg, inv_mul_cancel_left]
      _ = (s t).val * z := by rw [Units.val_mul, mul_assoc, hk]
  refine ⟨t, a, ht ▸ hr, ha, hmove, ?_⟩
  intro u b hu
  have to_orbit (c : Rˣ) (m : Multiplicative ℝ)
      (e : (c⁻¹).val * (g.val * z) = (s m).val * z) :
      g.val * z = (c * s m).val * z :=
    (unit_mul_left_cancel c⁻¹).mp (by simpa [Units.val_mul, ← mul_assoc] using e)
  have ea := to_orbit a t hmove
  have shift : (a * s t) * (b / a) = b * s t := by
    calc
      _ = (s t) * (a * (b / a)) := by ac_rfl
      _ = _ := by rw [mul_div_cancel, mul_comm]
  constructor
  · rintro ⟨hb, hb'⟩
    have eb := to_orbit b u hb'
    let c := (a * s t) / (b * s u)
    have hc : c.val * z = z := by
      apply (unit_mul_left_cancel (b * s u)).mp
      rw [← mul_assoc, ← Units.val_mul, show (b * s u) * c = a * s t by exact mul_div_cancel _ _]
      exact ea.symm.trans eb
    have hcn : N c = Real.exp t.toAdd / Real.exp u.toAdd := by simp [c, ha, hb, hs]
    obtain ⟨m, hm⟩ := (hZ _).mp ⟨c, hc, hcn⟩
    have htu : u = t := Multiplicative.toAdd.injective (Real.exp_injective
      (interval_ratio_eq_one hq (ht ▸ hr) hu m hm).symm)
    subst u
    refine ⟨rfl, (hH _).mpr ⟨?_, by rw [map_div, hb, ha, div_one]⟩⟩
    apply (unit_mul_left_cancel (a * s t)).mp
    rw [← mul_assoc, ← Units.val_mul,
      shift]
    exact eb.symm.trans ea
  · rintro ⟨rfl, hb⟩
    obtain ⟨hfix, hn'⟩ := (hH _).mp hb
    refine ⟨?_, ?_⟩
    · rwa [map_div, ha, div_one] at hn'
    · have eb : (b * s t).val * z = g.val * z := by
        rw [← shift,
          Units.val_mul, mul_assoc, hfix, ← ea]
      change (b⁻¹).val * (g.val * z) = _
      rw [← eb, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

private theorem finiteLocalUnit_norms (v : Place F) (r : ℝ) :
    (∃ u : (v.adicCompletion F)ˣ, ‖u.val‖ = r) ↔
      ∃ n : ℤ, r = (v.asIdeal.absNorm : ℝ) ^ n := by
  let π := chosenFiniteUniformizer F v
  have hπ := chosenFiniteUniformizer_spec F v
  have hnorm : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := norm_finiteUniformizer F v _ hπ
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨n, hn⟩ := finiteCompletion_norm_zpow F v π hπ u.val u.ne_zero
    refine ⟨-n, ?_⟩
    rw [hn, hnorm, inv_zpow, zpow_neg]
  · rintro ⟨n, rfl⟩
    refine ⟨π ^ (-n), ?_⟩
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, inv_zpow, zpow_neg, inv_inv]

private theorem finiteLocalUnit_integral_iff (v : Place F) (u : (v.adicCompletion F)ˣ) :
    u ∈ (v.adicCompletionIntegers F).toSubmonoid.units ↔ ‖u.val‖ = 1 :=
  (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).trans
    (finiteCompletion_norm_eq_one_iff F v u).symm

private theorem singleFiniteIdele_coordinate (v w : Place F) (u : (v.adicCompletion F)ˣ) :
    (singleFiniteIdele F v u).val.2 w =
      Function.update (fun x : Place F ↦ (1 : x.adicCompletion F)) v u.val w := rfl

/-- Insert a unit at the chosen finite place in the S-local group. -/
def sSingleFiniteIdele (S : Finset (Place F)) (v : S) (u : (v.val.adicCompletion F)ˣ) :
    (SAdeles F S)ˣ :=
  Units.map (sAdelesProjection F S) (singleFiniteIdele F v.val u)

theorem sSingleFiniteIdele_norm (S : Finset (Place F)) (v : S) (u : (v.val.adicCompletion F)ˣ) :
    sLocalIdeleNorm F S (sSingleFiniteIdele F S v u) = ‖u.val‖ := by
  let a := singleFiniteIdele F v.val u
  have ha : a ∈ sIdeleBlock F S := by
    apply (sIdeleBlock_mem_iff F S _).mpr
    intro w hw
    apply (ideleOrder_eq_zero_iff F _ w).mpr
    have hne : w ≠ v.val := fun h ↦ hw (h.symm ▸ v.property)
    change Valued.v (a.val.2 w) = 1
    rw [singleFiniteIdele_coordinate, Function.update_of_ne hne, map_one]
  exact (sBlock_norm_eq F S ⟨a, ha⟩).trans (singleFiniteIdele_norm F v.val u)

private def finiteUnitCoord (v : Place F) (a : Idele F) : (v.adicCompletion F)ˣ :=
  let e : Adeles F →* v.adicCompletion F :=
    { toFun := fun x ↦ x.2 v
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  Units.map e a

private def sFiniteUnitCoord (S : Finset (Place F)) (v : S) (a : (SAdeles F S)ˣ) :
    (v.val.adicCompletion F)ˣ :=
  let e : SAdeles F S →* v.val.adicCompletion F :=
    { toFun := fun x ↦ x.2 v
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  Units.map e a

/-- The stabilizer of the global finite coordinate point is the inserted local multiplicative group. -/
theorem adelic_finite_coordinate_stabilizer (v : Place F) (a : Idele F) :
    a.val * adelicCoordinatePoint F (.inr v) = adelicCoordinatePoint F (.inr v) ↔
      ∃ u : (v.adicCompletion F)ˣ, singleFiniteIdele F v u = a := by
  constructor
  · intro h
    refine ⟨finiteUnitCoord F v a, Units.ext (Prod.ext ?_ ?_)⟩
    · have he := congrArg Prod.fst h
      change a.val.1 * 1 = 1 at he
      change (1 : InfiniteAdeleRing F) = a.val.1
      simpa using he.symm
    · apply DFunLike.ext
      intro w
      rw [singleFiniteIdele_coordinate]
      by_cases hw : w = v
      · subst w
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne hw]
        have he := congrArg (fun x : Adeles F ↦ x.2 w) h
        change a.val.2 w * (if w = v then 0 else 1) = (if w = v then 0 else 1) at he
        simpa [hw] using he.symm
  · rintro ⟨u, rfl⟩
    apply Prod.ext
    · change (1 : InfiniteAdeleRing F) * 1 = 1
      simp
    · apply DFunLike.ext
      intro w
      change (singleFiniteIdele F v u).val.2 w * (if w = v then 0 else 1) =
        (if w = v then 0 else 1)
      by_cases hw : w = v
      · simp [hw]
      · rw [singleFiniteIdele_coordinate, Function.update_of_ne hw]
        simp [hw]

private theorem sAdelic_finite_point_apply (S : Finset (Place F)) (v w : S) :
    (sAdelicCoordinatePoint F S (.inr v)).2 w = if w = v then 0 else 1 := by
  change Function.update (1 : (j : S) → j.val.adicCompletion F) v 0 w =
    (if w = v then 0 else 1)
  by_cases h : w = v
  · subst w
    rw [Function.update_self, ite_eq_left rfl]
  · rw [Function.update_of_ne h, ite_eq_right h]
    rfl

/-- The stabilizer of the S-local finite coordinate point is the same local group. -/
theorem sAdelic_finite_coordinate_stabilizer (S : Finset (Place F)) (v : S) (a : (SAdeles F S)ˣ) :
    a.val * sAdelicCoordinatePoint F S (.inr v) = sAdelicCoordinatePoint F S (.inr v) ↔
      ∃ u : (v.val.adicCompletion F)ˣ, sSingleFiniteIdele F S v u = a := by
  constructor
  · intro h
    refine ⟨sFiniteUnitCoord F S v a, Units.ext (Prod.ext ?_ ?_)⟩
    · have he := congrArg Prod.fst h
      change a.val.1 * 1 = 1 at he
      change (1 : InfiniteAdeleRing F) = a.val.1
      simpa using he.symm
    · funext w
      change (singleFiniteIdele F v.val (sFiniteUnitCoord F S v a)).val.2 w.val = _
      rw [singleFiniteIdele_coordinate]
      by_cases hw : w = v
      · subst w
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne (fun h ↦ hw (Subtype.ext h))]
        have he := congrArg (fun x : SAdeles F S ↦ x.2 w) h
        change a.val.2 w * (sAdelicCoordinatePoint F S (.inr v)).2 w =
          (sAdelicCoordinatePoint F S (.inr v)).2 w at he
        simpa [sAdelic_finite_point_apply, hw] using he.symm
  · rintro ⟨u, rfl⟩
    apply Prod.ext
    · change (1 : InfiniteAdeleRing F) * 1 = 1
      simp
    · funext w
      change (singleFiniteIdele F v.val u).val.2 w.val * (sAdelicCoordinatePoint F S (.inr v)).2 w =
        (sAdelicCoordinatePoint F S (.inr v)).2 w
      rw [sAdelic_finite_point_apply]
      by_cases hw : w = v
      · simp [hw]
      · rw [singleFiniteIdele_coordinate, Function.update_of_ne (fun h ↦ hw (Subtype.ext h)),
          ite_eq_right hw, mul_one]

private theorem finite_coordinate_modulus_range {G U : Type*} (P : G → Prop)
    (N : G → ℝ) (j : U → G) (n : U → ℝ)
    (hP : ∀ g, P g ↔ ∃ u, j u = g) (hN : ∀ u, N (j u) = n u) (r : ℝ) :
    (∃ g, P g ∧ N g = r) ↔ ∃ u, n u = r := by
  constructor
  · rintro ⟨g, hg, hn⟩
    obtain ⟨u, rfl⟩ := (hP g).mp hg
    exact ⟨u, (hN u).symm.trans hn⟩
  · rintro ⟨u, hu⟩
    exact ⟨j u, (hP _).mpr ⟨u, rfl⟩, (hN u).trans hu⟩

private theorem finite_coordinate_normOne_stabilizer {G U : Type*} (P : G → Prop)
    (N : G → ℝ) (j : U → G) (H : Set U) (n : U → ℝ)
    (hP : ∀ g, P g ↔ ∃ u, j u = g) (hN : ∀ u, N (j u) = n u)
    (hU : ∀ u, u ∈ H ↔ n u = 1) (g : G) :
    g ∈ j '' H ↔ P g ∧ N g = 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(hP _).mpr ⟨u, rfl⟩, (hN u).trans ((hU u).mp hu)⟩
  · rintro ⟨hg, hn⟩
    obtain ⟨u, rfl⟩ := (hP g).mp hg
    exact ⟨u, (hU u).mpr ((hN u).symm.trans hn), rfl⟩

/-- The repaired global clause of 8.2.0.4. The parameter is unique and the
norm-one transporters form one coset of the inserted local integer-ring units. -/
theorem adelic_finite_orbit_fundamentalInterval (v : Place F)
    (s : Multiplicative ℝ →* Idele F)
    (hs : ∀ t, ideleNorm F (s t) = Real.exp t.toAdd)
    {x : Adeles F} (hx : x ∈ range (fun g : Idele F ↦ g.val * adelicCoordinatePoint F (.inr v))) :
    let z := adelicCoordinatePoint F (.inr v)
    let I := Ico 1 (v.asIdeal.absNorm : ℝ)
    let H := singleFiniteIdele F v '' (v.adicCompletionIntegers F).toSubmonoid.units
    ∃ (t : Multiplicative ℝ) (a : Idele F),
      Real.exp t.toAdd ∈ I ∧ ideleNorm F a = 1 ∧ (a⁻¹).val * x = (s t).val * z ∧
      ∀ (u : Multiplicative ℝ) (b : Idele F), Real.exp u.toAdd ∈ I →
        (ideleNorm F b = 1 ∧ (b⁻¹).val * x = (s u).val * z ↔ u = t ∧ b / a ∈ H) := by
  apply normOne_orbit_fundamentalInterval (ideleNorm F) (ideleNorm_pos F) _
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v) _ s hs _ _ hx
  · intro r
    exact (finite_coordinate_modulus_range _ _ _ _ (adelic_finite_coordinate_stabilizer F v)
      (singleFiniteIdele_norm F v) r).trans (finiteLocalUnit_norms F v r)
  · exact finite_coordinate_normOne_stabilizer _ _ _ _ _
      (adelic_finite_coordinate_stabilizer F v) (singleFiniteIdele_norm F v)
      (finiteLocalUnit_integral_iff F v)

/-- The repaired S-local clause of 8.2.0.4, for every set of selected finite places. -/
theorem sAdelic_finite_orbit_fundamentalInterval (S : Finset (Place F)) (v : S)
    (s : Multiplicative ℝ →* (SAdeles F S)ˣ)
    (hs : ∀ t, sLocalIdeleNorm F S (s t) = Real.exp t.toAdd)
    {x : SAdeles F S}
    (hx : x ∈ range (fun g : (SAdeles F S)ˣ ↦ g.val * sAdelicCoordinatePoint F S (.inr v))) :
    let z := sAdelicCoordinatePoint F S (.inr v)
    let I := Ico 1 (v.val.asIdeal.absNorm : ℝ)
    let H := sSingleFiniteIdele F S v '' (v.val.adicCompletionIntegers F).toSubmonoid.units
    ∃ (t : Multiplicative ℝ) (a : (SAdeles F S)ˣ),
      Real.exp t.toAdd ∈ I ∧ sLocalIdeleNorm F S a = 1 ∧ (a⁻¹).val * x = (s t).val * z ∧
      ∀ (u : Multiplicative ℝ) (b : (SAdeles F S)ˣ), Real.exp u.toAdd ∈ I →
        (sLocalIdeleNorm F S b = 1 ∧ (b⁻¹).val * x = (s u).val * z ↔ u = t ∧ b / a ∈ H) := by
  apply normOne_orbit_fundamentalInterval (sLocalIdeleNorm F S)
    (fun g ↦ ideleNorm_pos F (sLocalEmbed F S g).val) _
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val) _ s hs _ _ hx
  · intro r
    exact (finite_coordinate_modulus_range _ _ _ _ (sAdelic_finite_coordinate_stabilizer F S v)
      (sSingleFiniteIdele_norm F S v) r).trans (finiteLocalUnit_norms F v.val r)
  · exact finite_coordinate_normOne_stabilizer _ _ _ _ _
      (sAdelic_finite_coordinate_stabilizer F S v) (sSingleFiniteIdele_norm F S v)
      (finiteLocalUnit_integral_iff F v.val)

end Masullo
