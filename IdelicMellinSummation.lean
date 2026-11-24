import ModulatedMellinStripBounds
import BruhatWholeQuotientStages
import IdelicCutoffKernel
import SpectralLimit

open Bornology Function MeasureTheory NumberField Set Topology
open scoped BigOperators

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- A summable Mellin majorant on a bounded family, from a polynomial joint count. The finitely
many directions can include torus directions as well as the modulus direction.
The estimate only needs one large frequency in each nonzero shell. -/
theorem bruhatCompactMellin_majorant_of_joint_count
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m)
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)] {J : Type*} [Fintype J]
    (direction : J → (Multiplicative ℝ →ₜ* G))
    (χ : (Σ n, Shell n) → PontryaginDual G) (σ : (Σ n, Shell n) → ℝ)
    (w : (Σ n, Shell n) → ℕ) {a b C : ℝ} (d : ℕ)
    (hstrip : ∀ i, σ i ∈ Icc a b)
    (hfreq : ∀ n (i : Shell n), n = 0 ∨ ∃ j,
      (2 : ℝ) ^ n ≤ ‖mellinOrbitSlope m (σ ⟨n, i⟩) (χ ⟨n, i⟩) (direction j)‖)
    (hcount : ∀ n, (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (B : Set (BruhatCompactTest G)) (hB : IsVonNBounded ℂ B) :
    ∃ u : (Σ n, Shell n) → ℝ, Summable u ∧ ∀ f ∈ B, ∀ i,
      (w i : ℝ) * ‖modulatedMellinIntegral μ m f.val (σ i) (χ i)‖ ≤ u i := by
  classical
  let I : Set ℝ := univ
  let L : BruhatCompactTest G →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨bruhatCompactTest_toModulatedExponentialInductive m I,
      bruhatCompactTest_continuous_inductiveDecay m I hm hms⟩
  let α : I := ⟨a, mem_univ _⟩
  let β : I := ⟨b, mem_univ _⟩
  have bound (D : List (ℂ × List (Multiplicative ℝ →ₜ* G))) :
      ∃ A > 0, ∀ f ∈ B, ∀ i, ‖modulatedMellinSymbol m D (σ i) (χ i) *
        modulatedMellinIntegral μ m f.val (σ i) (χ i)‖ ≤ A := by
    obtain ⟨A, hA, h⟩ := modulatedMellin_symbol_norm_le_on_substrip μ m hm hms
      (L '' B) (hB.image L) α β D
    exact ⟨A, hA, fun f hf i => h (L f) ⟨f, hf, rfl⟩ ⟨σ i, mem_univ _⟩
      (hstrip i).1 (hstrip i).2 (χ i)⟩
  let p := d + 1
  obtain ⟨A₀, hA₀, h₀⟩ := bound [(1, [])]
  choose A hA h using fun j : J => bound [(1, List.replicate p (direction j))]
  let M := A₀ + ∑ j, A j
  have hM : 0 ≤ M :=
    add_nonneg hA₀.le (Finset.sum_nonneg fun j _ => (hA j).le)
  have hC : 0 ≤ C := by
    simpa using (Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Shell 0))) =>
      Nat.cast_nonneg (α := ℝ) (w ⟨0, i⟩)).trans (hcount 0)
  have hMellin (f : BruhatCompactTest G) (hf : f ∈ B) (n : ℕ) (i : Shell n) :
      ‖modulatedMellinIntegral μ m f.val (σ ⟨n, i⟩) (χ ⟨n, i⟩)‖ ≤
        M / ((2 : ℝ) ^ p) ^ n := by
    rcases hfreq n i with rfl | ⟨j, hj⟩
    · simp only [pow_zero, div_one]
      exact (by simpa [modulatedMellinSymbol] using h₀ f hf ⟨0, i⟩ : _ ≤ A₀).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => (hA k).le))
    · apply (le_div_iff₀ (by positivity)).mpr
      have hp : ((2 : ℝ) ^ p) ^ n ≤
          ‖mellinOrbitSlope m (σ ⟨n, i⟩) (χ ⟨n, i⟩) (direction j)‖ ^ p := by
        rw [← pow_mul, mul_comm p n, pow_mul]
        gcongr
      have hterm := h j f hf ⟨n, i⟩
      simp only [modulatedMellinSymbol, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, one_mul, List.map_replicate, List.prod_replicate,
        norm_mul, norm_pow] at hterm
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ ≤ A j := by simpa only [mul_comm] using hterm
        _ ≤ M := (Finset.single_le_sum (fun k _ => (hA k).le) (Finset.mem_univ j)).trans
          (le_add_of_nonneg_left hA₀.le)
  let u (i : Σ n, Shell n) := (w i : ℝ) * (M / ((2 : ℝ) ^ p) ^ i.1)
  refine ⟨u, ?_, fun f hf i => mul_le_mul_of_nonneg_left (hMellin f hf i.1 i.2) (by positivity)⟩
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  apply (summable_geometric_two.mul_left (M * C)).of_nonneg_of_le
  · exact fun _ => tsum_nonneg fun _ => by positivity
  · intro n
    rw [tsum_fintype]
    calc
      _ = (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) * (M / ((2 : ℝ) ^ p) ^ n) := by
        rw [Finset.sum_mul]
      _ ≤ (C * ((2 : ℝ) ^ d) ^ n) * (M / ((2 : ℝ) ^ p) ^ n) :=
        mul_le_mul_of_nonneg_right (hcount n) (by positivity)
      _ = (M * C) * (1 / 2 : ℝ) ^ n := by
        dsimp [p]
        rw [pow_succ, mul_pow, div_pow, one_pow]
        field_simp

/-- Absolute Mellin summability from a polynomial joint count. The finitely
many directions can include torus directions as well as the modulus direction.
The estimate only needs one large frequency in each nonzero shell. -/
theorem bruhatCompactMellin_summable_of_joint_count
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m)
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)] {J : Type*} [Fintype J]
    (direction : J → (Multiplicative ℝ →ₜ* G))
    (χ : (Σ n, Shell n) → PontryaginDual G) (σ : (Σ n, Shell n) → ℝ)
    (w : (Σ n, Shell n) → ℕ) {a b C : ℝ} (d : ℕ)
    (hstrip : ∀ i, σ i ∈ Icc a b)
    (hfreq : ∀ n (i : Shell n), n = 0 ∨ ∃ j,
      (2 : ℝ) ^ n ≤ ‖mellinOrbitSlope m (σ ⟨n, i⟩) (χ ⟨n, i⟩) (direction j)‖)
    (hcount : ∀ n, (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (f : BruhatCompactTest G) :
    Summable (fun i => (w i : ℝ) * ‖modulatedMellinIntegral μ m f.val (σ i) (χ i)‖) := by
  obtain ⟨u, hu, h⟩ := bruhatCompactMellin_majorant_of_joint_count μ m hm hms direction
    χ σ w d hstrip hfreq hcount {f} (isVonNBounded_singleton f)
  exact hu.of_nonneg_of_le (fun _ => by positivity) (h f (mem_singleton f))

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- A term outside the annihilator of an invariance subgroup in the modulus
kernel vanishes on the original group Haar measure. -/
theorem modulatedMellinIntegral_eq_zero_of_invariance
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ)
    (f : G → ℂ) (a : ℝ) (χ : PontryaginDual G) (k : G)
    (hm : m k = 1) (hf : ∀ x, f (k * x) = f x) (hχ : χ k ≠ 1) :
    modulatedMellinIntegral μ m f a χ = 0 := by
  let g (x : G) := modulatedExponentialWeight m a f x * (χ x : ℂ)
  change (∫ x, g x ∂μ) = 0
  have hmul (x : G) : g (k * x) = (χ k : ℂ) * g x := by
    dsimp only [g]
    rw [modulatedExponentialWeight_apply, modulatedExponentialWeight_apply,
      map_mul m, hm, one_mul, hf, map_mul χ, Circle.coe_mul]
    ring
  have h := integral_mul_left_eq_self (μ := μ) g k
  simp_rw [hmul, integral_const_mul] at h
  have hn : (χ k : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr fun he => hχ (Subtype.ext he)
  apply (mul_eq_zero.mp ?_).resolve_left hn
  rw [sub_mul, h, one_mul, sub_self]

/-- A common invariance subgroup eliminates the same indices for the entire
bounded family. The count and summable majorant only use surviving indices. -/
theorem modulatedMellin_majorant_of_invariant_joint_count
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m)
    (B : Set (BruhatCompactTest G)) (hB : IsVonNBounded ℂ B)
    {H : Type*} (ι : H → G) (hH : ∀ k, m (ι k) = 1)
    (hf : ∀ f ∈ B, ∀ k : H, ∀ x, f.val.val ((ι k) * x) = f.val.val x)
    {Z : Type*} (χ : Z → PontryaginDual (G)) (σ : Z → ℝ) (w : Z → ℕ)
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)] {J : Type*} [Fintype J]
    (direction : J → (Multiplicative ℝ →ₜ* G))
    (e : (Σ n, Shell n) ≃ {z : Z // ∀ k : H, χ z (ι k) = 1})
    {a b C : ℝ} (d : ℕ) (hstrip : ∀ i, σ (e i).val ∈ Icc a b)
    (hfreq : ∀ n (i : Shell n), n = 0 ∨ ∃ j,
      (2 : ℝ) ^ n ≤ |(mellinOrbitSlope (G := G) m 0
        (χ (e ⟨n, i⟩).val) (direction j)).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w (e ⟨n, i⟩).val : ℝ)) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (r : ℝ) (S : Set Z) :
    ∃ u : S → ℝ, Summable u ∧ ∀ f ∈ B, ∀ z : S,
      (w z.val : ℝ) * ‖modulatedMellinIntegral μ m f.val (σ z.val + r) (χ z.val)‖ ≤ u z := by
  classical
  obtain ⟨v, hv, h⟩ :=
    bruhatCompactMellin_majorant_of_joint_count μ m hm hms direction
      (fun i => χ (e i).val) (fun i => σ (e i).val + r) (fun i => w (e i).val)
      (a := a + r) (b := b + r) d
      (fun i => ⟨by linarith [(hstrip i).1], by linarith [(hstrip i).2]⟩)
      (fun n i => (hfreq n i).imp_right fun ⟨j, hj⟩ => ⟨j, hj.trans (by
        have he : (mellinOrbitSlope m 0 (χ (e ⟨n, i⟩).val) (direction j)).im =
            (mellinOrbitSlope m (σ (e ⟨n, i⟩).val + r)
              (χ (e ⟨n, i⟩).val) (direction j)).im := by
          simp [mellinOrbitSlope]
        rw [he]
        exact Complex.abs_im_le_norm _)⟩) hcount B hB
  let T : Set Z := {z | ∀ k : H, χ z (ι k) = 1}
  let u (z : Z) : ℝ := if hz : z ∈ T then v (e.symm ⟨z, hz⟩) else 0
  have hu : Summable u := by
    have hT : Summable (fun z : T => u z.val) :=
      e.summable_iff.mp (hv.congr fun i => by
        have hi : (e i).val ∈ T := (e i).property
        change v i = u (e i).val
        simp only [u, dite_eq_left hi, Subtype.coe_eta, Equiv.symm_apply_apply])
    refine ((summable_subtype_iff_indicator (s := T) (f := u)).mp hT).congr ?_
    intro z
    by_cases hz : z ∈ T
    · exact indicator_of_mem hz u
    · simp only [indicator_of_notMem hz, u, dite_eq_right hz]
  refine ⟨fun z => u z.val, hu.comp_injective Subtype.val_injective, fun f hfB z => ?_⟩
  by_cases hz : z.val ∈ T
  · simpa only [u, dite_eq_left hz, Equiv.apply_symm_apply] using h f hfB (e.symm ⟨z.val, hz⟩)
  · have hex : ∃ k : H, χ z.val (ι k) ≠ 1 := by
      simpa only [T, mem_ofPred_eq, not_forall] using hz
    obtain ⟨k, hk⟩ := hex
    have hzM := modulatedMellinIntegral_eq_zero_of_invariance μ m f.val (σ z.val + r)
      (χ z.val) (ι k) (hH k) (hf f hfB k) hk
    simp only [hzM, norm_zero, mul_zero, u, dite_eq_right hz, le_refl]

/-- Mellin summability for a test invariant under elements of the modulus kernel. Test
invariance removes all indices outside the annihilator. A polynomial joint
count, with multiplicity, is required only on the surviving samples.
Every real twist and every subset of the original family is allowed. -/
theorem modulatedMellin_summable_of_invariant_joint_count
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m)
    (f : BruhatCompactTest (G))
    {H : Type*} (ι : H → G) (hH : ∀ k, m (ι k) = 1)
    (hf : ∀ k : H, ∀ x, f.val.val ((ι k) * x) = f.val.val x)
    {Z : Type*} (χ : Z → PontryaginDual (G)) (σ : Z → ℝ) (w : Z → ℕ)
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)] {J : Type*} [Fintype J]
    (direction : J → (Multiplicative ℝ →ₜ* G))
    (e : (Σ n, Shell n) ≃ {z : Z // ∀ k : H, χ z (ι k) = 1})
    {a b C : ℝ} (d : ℕ) (hstrip : ∀ i, σ (e i).val ∈ Icc a b)
    (hfreq : ∀ n (i : Shell n), n = 0 ∨ ∃ j,
      (2 : ℝ) ^ n ≤ |(mellinOrbitSlope (G := G) m 0
        (χ (e ⟨n, i⟩).val) (direction j)).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w (e ⟨n, i⟩).val : ℝ)) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (r : ℝ) (S : Set Z) :
    Summable (fun z : S => (w z.val : ℝ) *
      ‖modulatedMellinIntegral μ m f.val (σ z.val + r) (χ z.val)‖) := by
  obtain ⟨u, hu, h⟩ := modulatedMellin_majorant_of_invariant_joint_count μ m hm hms
    {f} (isVonNBounded_singleton f) ι hH (fun g hg => mem_singleton_iff.mp hg ▸ hf)
    χ σ w direction e d hstrip hfreq hcount r S
  exact hu.of_nonneg_of_le (fun _ => by positivity) (h f (mem_singleton f))

section IdeleClass

variable (F : Type*) [Field F] [NumberField F]

local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

/-- The logarithmic modulus on the idele class group as a continuous homomorphism. -/
def mellinClassModulus : IdeleClass F →ₜ* Multiplicative ℝ :=
  ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩

set_option maxHeartbeats 900000 in
/-- One compact subgroup of the norm-one classes fixes every test in a bounded
family and has open compactly generated annihilator. -/
theorem ideleClassMellin_exists_bounded_invariance
    (B : Set (BruhatCompactTest (IdeleClass F))) (hB : IsVonNBounded ℂ B) :
    ∃ H : Subgroup (normOneIdeleClass F), IsCompact (H : Set (normOneIdeleClass F)) ∧
      IsOpen (lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype) :
        Set (PontryaginDual (IdeleClass F))) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype)) ∧
      ∀ f ∈ B, ∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m := mellinClassModulus F
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m :=
    fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  let L := bruhatCompactTest_toSchwartz (G := IdeleClass F)
  obtain ⟨p, C, _, hC⟩ := (bruhatSchwartz_strict (G := IdeleClass F)).2.2 (L '' B) (hB.image L)
  obtain ⟨Q, hQ⟩ := exists_wholeBruhatStage_refinement m hm hms p
  let P := Q.val.1
  let H := P.kernel.comap (normOneIdeleClass F).subtype
  have hle : P.kernel ≤ normOneIdeleClass F := by
    intro x hx
    have hxlog := P.modulation_eq_one_on_kernel (mellinClassModulus F) ⟨x, hx⟩
    have hxexp := congrArg (fun t : Multiplicative ℝ => Real.exp t.toAdd) hxlog
    change Real.exp (Real.log (ideleClassNorm F x)) = Real.exp 0 at hxexp
    exact (Real.exp_log (ideleClassNorm_pos F x)).symm.trans (hxexp.trans Real.exp_zero)
  have hmap : H.map (normOneIdeleClass F).subtype = P.kernel := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  refine ⟨H, (P.kernel_closed.preimage continuous_subtype_val).isCompact, ?_, ?_, ?_⟩
  · rw [hmap]
    exact P.annihilator_open
  · rw [hmap]
    exact P.annihilator_compactlyGenerated
  · intro f hf k x
    obtain ⟨u, _, hu⟩ := hC.symm ▸ (show L f ∈ L '' B from ⟨f, hf, rfl⟩)
    let w := p.transition Q.val hQ u
    have hw : Q.val.realize w = f.val.val :=
      congrArg Subtype.val ((p.inclusion_transition Q.val hQ u).trans hu)
    have hk : Q.coordinates k.val.val = 1 := by
      have hk' : k.val.val ∈ Q.val.1.kernel := k.property
      rwa [← Q.coordinates_ker] at hk'
    have he : Q.coordinates (k.val.val * x) = Q.coordinates x :=
      (map_mul Q.coordinates k.val.val x).trans ((congrArg (· * Q.coordinates x) hk).trans (one_mul _))
    calc
      f.val.val (k.val.val * x) = Q.val.realize w (k.val.val * x) := (congrFun hw _).symm
      _ = Q.val.realize w x := (Q.realize_eq_coordinates w _).trans
        ((congrArg (fun y => w.val y.toAdd) he).trans (Q.realize_eq_coordinates w x).symm)
      _ = f.val.val x := congrFun hw _

/-- Every compact Bruhat test has a compact subgroup of invariance inside
the norm-one idele classes, with open compactly generated annihilator. -/
theorem ideleClassMellin_exists_compact_invariance (f : BruhatCompactTest (IdeleClass F)) :
    ∃ H : Subgroup (normOneIdeleClass F), IsCompact (H : Set (normOneIdeleClass F)) ∧
      IsOpen (lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype) :
        Set (PontryaginDual (IdeleClass F))) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype)) ∧
      ∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x := by
  obtain ⟨H, hc, ho, hg, hi⟩ :=
    ideleClassMellin_exists_bounded_invariance F {f} (isVonNBounded_singleton f)
  exact ⟨H, hc, ho, hg, hi f (mem_singleton f)⟩

set_option maxHeartbeats 1600000 in
/-- The quantitative implication in B.4.4.9 on actual idele classes. Test
invariance removes all indices outside the annihilator. A polynomial joint
count, with multiplicity, is required only on the surviving samples.
Every real twist and every subset of the original family is allowed. -/
theorem ideleClassMellin_summable_of_joint_count
    (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]
    (f : BruhatCompactTest (IdeleClass F))
    (H : Subgroup (normOneIdeleClass F)) (hf : ∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x)
    {Z : Type*} (χ : Z → PontryaginDual (IdeleClass F)) (σ : Z → ℝ) (w : Z → ℕ)
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)] {J : Type*} [Fintype J]
    (direction : J → (Multiplicative ℝ →ₜ* IdeleClass F))
    (e : (Σ n, Shell n) ≃ {z : Z // ∀ k : H, χ z k.val.val = 1})
    {a b C : ℝ} (d : ℕ) (hstrip : ∀ i, σ (e i).val ∈ Icc a b)
    (hfreq : ∀ n (i : Shell n), n = 0 ∨ ∃ j,
      (2 : ℝ) ^ n ≤ |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0
        (χ (e ⟨n, i⟩).val) (direction j)).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w (e ⟨n, i⟩).val : ℝ)) ≤ C * ((2 : ℝ) ^ d) ^ n)
    (r : ℝ) (S : Set Z) :
    Summable (fun z : S => (w z.val : ℝ) *
      ‖∫ g, f.val.val g * (Real.exp ((σ z.val + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
        (χ z.val g : ℂ) ∂μ‖) := by
  classical
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m := mellinClassModulus F
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m :=
    fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  have hH : ∀ k : H, m k.val.val = 1 := by
    intro k
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val.val)) = 1
    rw [show ideleClassNorm F k.val.val = 1 from k.val.property, Real.log_one]
    rfl
  have hs := modulatedMellin_summable_of_invariant_joint_count μ m hm hms f
    (fun k : H => k.val.val) hH hf χ σ w direction e d hstrip hfreq hcount r S
  refine hs.congr ?_
  intro z
  apply congrArg ((w z.val : ℝ) * ·)
  apply congrArg norm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (((Real.exp ((σ z.val + r) * (ideleClassLogNorm F x).toAdd) : ℝ) : ℂ) *
      f.val.val x) * (χ z.val x : ℂ) = _
    exact congrArg (· * (χ z.val x : ℂ)) (mul_comm _ _)

end IdeleClass

end
end Masullo
