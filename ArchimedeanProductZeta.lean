import ArchimedeanZetaContraction
import ArchimedeanMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.MeasureTheory.Integral.Pi

open Filter MeasureTheory NumberField Set Topology
open scoped Classical ENNReal SchwartzMap

namespace Masullo

noncomputable section

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private def splitFinCoordinate (n : ℕ) (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    (Fin (n + 1) → X) ≃L[ℝ] X × (Fin n → X) where
  toFun x := (x 0, Fin.tail x)
  invFun p := Fin.cons p.1 p.2
  left_inv := Fin.cons_self_tail
  right_inv p := by
    change (Fin.cons (α := fun _ => X) p.1 p.2 0, Fin.tail (Fin.cons (α := fun _ => X) p.1 p.2)) = p
    rw [Fin.cons_zero, Fin.tail_cons]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (continuous_fst : Continuous (fun p : X × (Fin n → X) => p.1))
    · simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp
        (continuous_snd : Continuous (fun p : X × (Fin n → X) => p.2))

private def splitRealCoordinate (n : ℕ) (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    ((Fin (n + 1) → ℝ) × Z) ≃L[ℝ] ℝ × ((Fin n → ℝ) × Z) :=
  ((splitFinCoordinate n ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ Z)).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ℝ (Fin n → ℝ) Z)

private def emptyContraction : 𝓢(Fin 0 → ℂ, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f 0) (fun _ _ => rfl) (fun _ _ => rfl)
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by
      simpa only [one_mul, Finset.sup_singleton, schwartzSeminormFamily] using SchwartzMap.norm_le_seminorm ℂ f 0⟩

/-- Continued zeta on a product of complex places, by successive angular
and Mellin contraction of the coordinates of a single coupled Schwartz test. -/
def complexPlacesZeta (ν : Measure Circle) [IsFiniteMeasure ν] :
    (n : ℕ) → (Fin n → ℂ × ℤ) → ℂ → 𝓢(Fin n → ℂ, ℂ) →L[ℂ] ℂ
  | 0, _, _ => emptyContraction
  | n + 1, j, s =>
    (complexPlacesZeta ν n (Fin.tail j) s).comp
      ((complexArchimedeanZetaInFirst ν (j 0).2 (s + (j 0).1)).comp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitFinCoordinate n ℂ).symm))

theorem complexPlacesZeta_meromorphicOperator (ν : Measure Circle) [IsFiniteMeasure ν] :
    ∀ (n : ℕ) (j : Fin n → ℂ × ℤ), MeromorphicOperator (complexPlacesZeta ν n j)
  | 0, _ => .const _
  | n + 1, j => (complexPlacesZeta_meromorphicOperator ν n (Fin.tail j)).comp
      ((complexArchimedeanZetaInFirst_meromorphicOperator ν (j 0).2 |>.translate (j 0).1).comp (.const _))

private def discardEmptyRealCoordinates (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    𝓢((Fin 0 → ℝ) × Z, ℂ) →L[ℂ] 𝓢(Z, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (ContinuousLinearMap.inr ℝ (Fin 0 → ℝ) Z).hasTemperateGrowth
    (K := 1) (by intro x y; simp [edist_dist, Prod.dist_eq])

/-- Continued zeta for an arbitrary finite product of real and complex
places. The tests may couple all coordinates. -/
def archimedeanPlacesZeta (ν : Measure Circle) [IsFiniteMeasure ν] (m : ℕ) (j : Fin m → ℂ × ℤ) :
    (n : ℕ) → (Fin n → ℂ × ℕ) → ℂ → 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ) →L[ℂ] ℂ
  | 0, _, s => (complexPlacesZeta ν m j s).comp (discardEmptyRealCoordinates (Fin m → ℂ))
  | n + 1, a, s =>
    (archimedeanPlacesZeta ν m j n (Fin.tail a) s).comp
      ((realArchimedeanZetaInFirst (a 0).2 (s + (a 0).1)).comp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitRealCoordinate n (Fin m → ℂ)).symm))

theorem archimedeanPlacesZeta_meromorphicOperator (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℕ) (j : Fin m → ℂ × ℤ) : ∀ (n : ℕ) (a : Fin n → ℂ × ℕ),
      MeromorphicOperator (archimedeanPlacesZeta ν m j n a)
  | 0, _ => (complexPlacesZeta_meromorphicOperator ν m j).comp (.const _)
  | n + 1, a => (archimedeanPlacesZeta_meromorphicOperator ν m j n (Fin.tail a)).comp
      (((realArchimedeanZetaInFirst_meromorphicOperator (a 0).2).translate (a 0).1).comp (.const _))

private theorem schwartz_uniform_continuous_seminorm
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ℂ → 𝓢(X, ℂ) →L[ℂ] 𝓢(Y, ℂ)) (U : Set ℂ)
    (h : ∀ k j : ℕ, ∃ p : Seminorm ℂ 𝓢(X, ℂ), Continuous p ∧
      ∀ z ∈ U, ∀ f, SchwartzMap.seminorm ℂ k j (L z f) ≤ p f)
    (q : Seminorm ℂ 𝓢(Y, ℂ)) (hq : Continuous q) :
    ∃ p : Seminorm ℂ 𝓢(X, ℂ), Continuous p ∧ ∀ z ∈ U, ∀ f, q (L z f) ≤ p f := by
  classical
  obtain ⟨J, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ Y ℂ) q hq
  have hs (i : ℕ × ℕ) := h i.1 i.2
  choose p hp hb using hs
  refine ⟨C • J.sup p, (Seminorm.continuous_finsetSup fun i _ ↦ hp i).const_smul C, ?_⟩
  intro z hz f
  refine (hC _).trans ?_
  simp only [smul_apply, NNReal.smul_def, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro i hi
  exact (hb i z hz f).trans (Seminorm.le_finset_sup_apply hi)

/-- The coordinate couplings in an archimedean test are retained in
the uniform strip bound for the continued product. -/
theorem complexPlacesZeta_uniform_seminorm (ν : Measure Circle) [IsFiniteMeasure ν]
    (l r : ℝ) : ∀ (n : ℕ) (j : Fin n → ℂ × ℤ),
    ∃ p : Seminorm ℂ 𝓢(Fin n → ℂ, ℂ), Continuous p ∧
      ∀ (s : ℂ), s.re ∈ Icc l r → (∀ i, 1 ≤ |(s + (j i).1).im|) → ∀ f,
        ‖complexPlacesZeta ν n j s f‖ ≤ p f
  | 0, _ => ⟨(normSeminorm ℂ ℂ).comp emptyContraction.toLinearMap,
      continuous_norm.comp emptyContraction.continuous, fun _ _ _ _ ↦ le_rfl⟩
  | n + 1, j => by
    obtain ⟨q, hq, htail⟩ := complexPlacesZeta_uniform_seminorm ν l r n (Fin.tail j)
    let α := (j 0).1
    let L := complexArchimedeanZetaInFirst (Y := Fin n → ℂ) ν (j 0).2
    let U := {z : ℂ | z.re ∈ Icc (l + α.re) (r + α.re) ∧ 1 ≤ |z.im|}
    obtain ⟨p, hp, hb⟩ := schwartz_uniform_continuous_seminorm L U
      (fun k d ↦ by
        obtain ⟨p, hp, hb⟩ := complexArchimedeanZetaInFirst_uniform_seminorm
          (Y := Fin n → ℂ) ν (j 0).2 (l + α.re) (r + α.re) k d
        exact ⟨p, hp, fun z hz ↦ hb z hz.1 hz.2⟩) q hq
    let T := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ (splitFinCoordinate n ℂ).symm
    refine ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun s hs hi f ↦ ?_⟩
    have hz : s + α ∈ U := ⟨by rw [Complex.add_re]; exact ⟨add_le_add hs.1 le_rfl, add_le_add hs.2 le_rfl⟩,
      hi 0⟩
    exact (htail s hs (fun i ↦ hi i.succ) (L (s + α) (T f))).trans (hb (s + α) hz (T f))

/-- The continued joint real and complex contraction is uniformly bounded
by a single continuous seminorm on any closed strip away from low heights. -/
theorem archimedeanPlacesZeta_uniform_seminorm (ν : Measure Circle) [IsFiniteMeasure ν]
    (l r : ℝ) (m : ℕ) (j : Fin m → ℂ × ℤ) : ∀ (n : ℕ) (a : Fin n → ℂ × ℕ),
    ∃ p : Seminorm ℂ 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ), Continuous p ∧
      ∀ (s : ℂ), s.re ∈ Icc l r → (∀ i, 1 ≤ |(s + (j i).1).im|) →
        (∀ i, 1 ≤ |(s + (a i).1).im|) → ∀ f, ‖archimedeanPlacesZeta ν m j n a s f‖ ≤ p f
  | 0, _ => by
    obtain ⟨p, hp, hb⟩ := complexPlacesZeta_uniform_seminorm ν l r m j
    let T := discardEmptyRealCoordinates (Fin m → ℂ)
    exact ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun s hs hj _ f ↦ hb s hs hj (T f)⟩
  | n + 1, a => by
    obtain ⟨q, hq, htail⟩ := archimedeanPlacesZeta_uniform_seminorm ν l r m j n (Fin.tail a)
    let α := (a 0).1
    let L := realArchimedeanZetaInFirst (Y := (Fin n → ℝ) × (Fin m → ℂ)) (a 0).2
    let U := {z : ℂ | z.re ∈ Icc (l + α.re) (r + α.re) ∧ 1 ≤ |z.im|}
    obtain ⟨p, hp, hb⟩ := schwartz_uniform_continuous_seminorm L U
      (fun k d ↦ by
        obtain ⟨p, hp, hb⟩ := realArchimedeanZetaInFirst_uniform_seminorm
          (Y := (Fin n → ℝ) × (Fin m → ℂ)) (a 0).2 (l + α.re) (r + α.re) k d
        exact ⟨p, hp, fun z hz ↦ hb z hz.1 hz.2⟩) q hq
    let T := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ (splitRealCoordinate n (Fin m → ℂ)).symm
    refine ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun s hs hj hi f ↦ ?_⟩
    have hz : s + α ∈ U := ⟨by rw [Complex.add_re]; exact ⟨add_le_add hs.1 le_rfl, add_le_add hs.2 le_rfl⟩,
      hi 0⟩
    exact (htail s hs hj (fun i ↦ hi i.succ) (L (s + α) (T f))).trans (hb (s + α) hz (T f))

/-- A parameter avoiding the real-place pole lattice for the sign parity. -/
def RealArchZetaRegular (a : ℕ) (s : ℂ) : Prop :=
  ∀ k : ℕ, s + k = 0 → Odd (a + k)

/-- A parameter avoiding the complex-place pole lattice for the angular frequency. -/
def ComplexArchZetaRegular (j : ℤ) (s : ℂ) : Prop :=
  ∀ k : ℕ, 2 * s + k = 0 → ¬ ∃ n : ℕ, k = j.natAbs + 2 * n

theorem realArchZetaRegular_iff_gamma (a : ℕ) (z : ℂ) :
    RealArchZetaRegular a z ↔ Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ)) ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff]
  constructor
  · rintro h ⟨n, hn⟩
    let k := a % 2 + 2 * n
    have hk : z + (k : ℂ) = 0 := by
      simp only [k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      linear_combination hn
    exact (Nat.not_odd_iff_even.mpr (Nat.even_iff.mpr (by dsimp [k]; omega))) (h k hk)
  · intro h k hk
    by_contra hodd
    have he := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
    have hkn : k = a % 2 + 2 * (k / 2) := by omega
    apply h
    refine ⟨k / 2, ?_⟩
    rw [show (k : ℂ) = ((a % 2 : ℕ) : ℂ) + 2 * ((k / 2 : ℕ) : ℂ) from by exact_mod_cast hkn] at hk
    linear_combination hk

theorem complexArchZetaRegular_iff_gamma (j : ℤ) (z : ℂ) :
    ComplexArchZetaRegular j z ↔ Complex.Gammaℂ (z + (j.natAbs : ℂ) / 2) ≠ 0 := by
  have hp : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hl : (2 : ℂ) * ((2 : ℂ) * (Real.pi : ℂ)) ^ (-(z + (j.natAbs : ℂ) / 2)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))
  rw [Complex.Gammaℂ_def, mul_ne_zero_iff, and_iff_right hl, ne_eq, Complex.Gamma_eq_zero_iff]
  constructor
  · rintro h ⟨n, hn⟩
    let k := j.natAbs + 2 * n
    have hk : 2 * z + (k : ℂ) = 0 := by
      simp only [k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      linear_combination 2 * hn
    exact h k hk ⟨n, rfl⟩
  · intro h k hk
    rintro ⟨n, rfl⟩
    apply h
    refine ⟨n, ?_⟩
    push_cast at hk
    linear_combination hk / 2

private theorem complexPlacesZeta_hasOperatorTaylorEstimate (c : ℂ) :
    ∀ (n : ℕ) (j : Fin n → ℂ × ℤ), (∀ i, ComplexArchZetaRegular (j i).2 (c + (j i).1)) →
      ∃ D, HasOperatorTaylorEstimate (complexPlacesZeta complexTamagawaAngularMeasure n j) c D
  | 0, _, _ => ⟨_, HasOperatorTaylorEstimate.const _ c⟩
  | n + 1, j, hj => by
    obtain ⟨_, htail⟩ := complexPlacesZeta_hasOperatorTaylorEstimate c n (Fin.tail j) (fun i => hj i.succ)
    obtain ⟨D, hhead⟩ := complexArchimedeanZetaInFirst_hasOperatorTaylorEstimate
      (Y := Fin n → ℂ) complexTamagawaAngularMeasure (j 0).2 (c + (j 0).1) (hj 0)
    have hs : HasOperatorTaylorEstimate
        (complexArchimedeanZetaInFirst (Y := Fin n → ℂ) complexTamagawaAngularMeasure (j 0).2)
        (1 * c + (j 0).1) D := by
      simpa only [one_mul] using hhead
    have hshift := hs.reparametrize 1 (j 0).1
    simp only [one_mul, one_smul] at hshift
    exact ⟨_, htail.comp (hshift.comp (HasOperatorTaylorEstimate.const _ c))⟩

private theorem archimedeanPlacesZeta_hasOperatorTaylorEstimate (m : ℕ) (j : Fin m → ℂ × ℤ)
    (c : ℂ) (hj : ∀ i, ComplexArchZetaRegular (j i).2 (c + (j i).1)) :
    ∀ (n : ℕ) (a : Fin n → ℂ × ℕ), (∀ i, RealArchZetaRegular (a i).2 (c + (a i).1)) →
      ∃ D, HasOperatorTaylorEstimate (archimedeanPlacesZeta complexTamagawaAngularMeasure m j n a) c D
  | 0, _, _ => by
    obtain ⟨_, h⟩ := complexPlacesZeta_hasOperatorTaylorEstimate c m j hj
    exact ⟨_, h.comp (HasOperatorTaylorEstimate.const _ c)⟩
  | n + 1, a, ha => by
    obtain ⟨_, htail⟩ := archimedeanPlacesZeta_hasOperatorTaylorEstimate m j c hj n
      (Fin.tail a) (fun i => ha i.succ)
    obtain ⟨D, hhead⟩ := realArchimedeanZetaInFirst_hasOperatorTaylorEstimate
      (Y := (Fin n → ℝ) × (Fin m → ℂ)) (a 0).2 (c + (a 0).1) (ha 0)
    have hs : HasOperatorTaylorEstimate
        (realArchimedeanZetaInFirst (Y := (Fin n → ℝ) × (Fin m → ℂ)) (a 0).2)
        (1 * c + (a 0).1) D := by
      simpa only [one_mul] using hhead
    have hshift := hs.reparametrize 1 (a 0).1
    simp only [one_mul, one_smul] at hshift
    exact ⟨_, htail.comp (hshift.comp (HasOperatorTaylorEstimate.const _ c))⟩

/-- The entire reciprocal Gamma factor at a real place. -/
def realArchZetaDenominator (a : ℕ) (z : ℂ) : ℂ :=
  (Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ)))⁻¹

/-- The entire reciprocal Gamma factor at a complex place. -/
def complexArchZetaDenominator (j : ℤ) (z : ℂ) : ℂ :=
  (Complex.Gammaℂ (z + (j.natAbs : ℂ) / 2))⁻¹

theorem realArchZetaDenominator_analytic (a : ℕ) (z : ℂ) :
    AnalyticAt ℂ (realArchZetaDenominator a) z :=
  (Complex.differentiable_Gammaℝ_inv.analyticAt _).comp (analyticAt_id.add analyticAt_const)

theorem complexArchZetaDenominator_analytic (j : ℤ) (z : ℂ) :
    AnalyticAt ℂ (complexArchZetaDenominator j) z :=
  (Complex.differentiable_Gammaℂ_inv.analyticAt _).comp (analyticAt_id.add analyticAt_const)

private theorem complexPlacesZeta_denominator_analyticOperatorGerm (c : ℂ) :
    ∀ (n : ℕ) (j : Fin n → ℂ × ℤ),
      AnalyticOperatorGerm (fun z =>
        (∏ i, complexArchZetaDenominator (j i).2 (z + (j i).1)) •
        complexPlacesZeta complexTamagawaAngularMeasure n j z) c
  | 0, _ => by simpa only [Fin.prod_univ_zero, one_smul, complexPlacesZeta] using
      AnalyticOperatorGerm.const (c := c) emptyContraction
  | n + 1, j => by
    have htail := complexPlacesZeta_denominator_analyticOperatorGerm c n (Fin.tail j)
    have hhead := complexArchimedeanZetaInFirst_analyticOperatorGerm
      (Y := Fin n → ℂ) complexTamagawaAngularMeasure (j 0).2
      (complexArchZetaDenominator_analytic (j 0).2 (c + (j 0).1)) (by
        intro k hk hp
        apply inv_eq_zero.mpr
        by_contra hne
        exact ((complexArchZetaRegular_iff_gamma _ _).mpr hne) k hk hp)
    have hshift := hhead.translate (j 0).1
    have hc := htail.comp_mul_smul (hshift.smul_comp_const
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitFinCoordinate n ℂ).symm))
    apply hc.congr (.of_forall fun z => ?_)
    ext f
    simp only [Fin.prod_univ_succ, complexPlacesZeta, ContinuousLinearMap.comp_apply,
      smul_apply, Fin.tail, mul_smul]
    rw [smul_comm (complexArchZetaDenominator (j 0).2 (z + (j 0).1))]

private theorem archimedeanPlacesZeta_denominator_analyticOperatorGerm
    (m : ℕ) (j : Fin m → ℂ × ℤ) (c : ℂ) :
    ∀ (n : ℕ) (a : Fin n → ℂ × ℕ), AnalyticOperatorGerm (fun z =>
      ((∏ i, realArchZetaDenominator (a i).2 (z + (a i).1)) *
        (∏ i, complexArchZetaDenominator (j i).2 (z + (j i).1))) •
      archimedeanPlacesZeta complexTamagawaAngularMeasure m j n a z) c
  | 0, _ => by
    apply ((complexPlacesZeta_denominator_analyticOperatorGerm c m j).comp
      (.const (discardEmptyRealCoordinates (Fin m → ℂ)))).congr (.of_forall fun z => ?_)
    ext f
    simp only [Fin.prod_univ_zero, one_mul, archimedeanPlacesZeta, ContinuousLinearMap.comp_apply,
      smul_apply]
  | n + 1, a => by
    have htail := archimedeanPlacesZeta_denominator_analyticOperatorGerm m j c n (Fin.tail a)
    have hhead := realArchimedeanZetaInFirst_analyticOperatorGerm
      (Y := (Fin n → ℝ) × (Fin m → ℂ)) (a 0).2
      (realArchZetaDenominator_analytic (a 0).2 (c + (a 0).1)) (by
        intro k hk hp
        apply inv_eq_zero.mpr
        by_contra hne
        exact (Nat.not_odd_iff_even.mpr hp) (((realArchZetaRegular_iff_gamma _ _).mpr hne) k hk))
    have hshift := hhead.translate (a 0).1
    have hc := htail.comp_mul_smul (hshift.smul_comp_const
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitRealCoordinate n (Fin m → ℂ)).symm))
    apply hc.congr (.of_forall fun z => ?_)
    ext f
    simp only [Fin.prod_univ_succ, archimedeanPlacesZeta, ContinuousLinearMap.comp_apply, smul_apply,
      Fin.tail, mul_smul]
    simp only [smul_eq_mul]
    ac_rfl

/-- The iterated local integrals in polar coordinates, with the first
indexed coordinate integrated first. -/
def complexPlacesZetaIterated (ν : Measure Circle) [IsFiniteMeasure ν] :
    (n : ℕ) → (Fin n → ℂ × ℤ) → ℂ → ((Fin n → ℂ) → ℂ) → ℂ
  | 0, _, _, f => f 0
  | n + 1, j, s, f =>
    complexPlacesZetaIterated ν n (Fin.tail j) s (fun x =>
      ∫ p : ℝ × Circle, ((p.1 : ℂ) ^ (2 * (s + (j 0).1) - 1) * (p.2 : ℂ) ^ (j 0).2) *
        f (Fin.cons (p.1 • (p.2 : ℂ)) x) ∂((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ν)

theorem complexPlacesZeta_eq_iterated (ν : Measure Circle) [IsFiniteMeasure ν]
    (s : ℂ) : ∀ (n : ℕ) (j : Fin n → ℂ × ℤ), (∀ i, 0 < (s + (j i).1).re) →
      ∀ f : 𝓢(Fin n → ℂ, ℂ), complexPlacesZeta ν n j s f = complexPlacesZetaIterated ν n j s f
  | 0, _, _, _ => rfl
  | n + 1, j, hs, f => by
    rw [complexPlacesZeta, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      complexPlacesZeta_eq_iterated ν s n (Fin.tail j) (fun i => hs i.succ), complexPlacesZetaIterated]
    congr 1
    funext x
    rw [complexArchimedeanZetaInFirst_eq_polar _ _ _ (hs 0), schwartzPolarMellin_apply]
    rfl

/-- The iterated integrals of all real and complex coordinates on the
original half-plane. Real powers use `dx / |x|` in the ambient coordinate. -/
def archimedeanPlacesZetaIterated (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℕ) (j : Fin m → ℂ × ℤ) : (n : ℕ) → (Fin n → ℂ × ℕ) → ℂ →
    (((Fin n → ℝ) × (Fin m → ℂ)) → ℂ) → ℂ
  | 0, _, s, f => complexPlacesZetaIterated ν m j s (fun y => f (0, y))
  | n + 1, a, s, f =>
    archimedeanPlacesZetaIterated ν m j n (Fin.tail a) s (fun p =>
      ∫ t : ℝ, ((|t| : ℝ) : ℂ) ^ (s + (a 0).1 - 1) *
        (if t < 0 then (-1 : ℂ) ^ (a 0).2 else 1) * f (Fin.cons t p.1, p.2))

theorem archimedeanPlacesZeta_eq_iterated (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℕ) (j : Fin m → ℂ × ℤ) (s : ℂ) (hj : ∀ i, 0 < (s + (j i).1).re) :
    ∀ (n : ℕ) (a : Fin n → ℂ × ℕ), (∀ i, 0 < (s + (a i).1).re) →
      ∀ f : 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ),
        archimedeanPlacesZeta ν m j n a s f = archimedeanPlacesZetaIterated ν m j n a s f
  | 0, _, _, f => by
    rw [archimedeanPlacesZeta, ContinuousLinearMap.comp_apply,
      complexPlacesZeta_eq_iterated ν s m j hj]
    rfl
  | n + 1, a, ha, f => by
    rw [archimedeanPlacesZeta, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      archimedeanPlacesZeta_eq_iterated ν m j s hj n (Fin.tail a) (fun i => ha i.succ),
      archimedeanPlacesZetaIterated]
    congr 1
    funext p
    rw [realArchimedeanZetaInFirst_eq_integral _ _ (ha 0)]
    rfl

/-- The real contraction is the weighted unit-group Haar integral on each
slice of a coupled test. -/
theorem realArchimedeanZetaInFirst_eq_unitIntegral {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (a : ℕ) (s : ℂ) (hs : 0 < s.re) (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    let g (u : ℝˣ) :=
      ((|(u : ℝ)| : ℝ) : ℂ) ^ s * (if (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) * f ((u : ℝ), y)
    Integrable g realArchMultiplicativeHaar ∧
      realArchimedeanZetaInFirst a s f y = ∫ u, g u ∂realArchMultiplicativeHaar := by
  simpa only [archimedeanSlice_apply, realArchimedeanZetaInFirst_apply] using
    realArchimedeanZetaContinued_eq_unitIntegral a (archimedeanSlice y f) hs

/-- The complex contraction is the weighted unit-group Haar integral on
each slice, in the normalized squared-radius coordinate. -/
theorem complexArchimedeanZetaInFirst_eq_unitIntegral {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]
    (j : ℤ) (s : ℂ) (hs : 0 < s.re) (f : 𝓢(ℂ × Y, ℂ)) (y : Y) :
    let g (u : ℂˣ) :=
      ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((u : ℂ) / (‖(u : ℂ)‖ : ℂ)) ^ j * f ((u : ℂ), y)
    Integrable g complexArchMultiplicativeHaar ∧
      complexArchimedeanZetaInFirst complexTamagawaAngularMeasure j s f y =
        ∫ u, g u ∂complexArchMultiplicativeHaar := by
  simpa only [archimedeanSlice_apply, complexArchimedeanZetaInFirst_apply] using
    complexArchimedeanZetaContinued_eq_unitIntegral j (archimedeanSlice y f) hs

attribute [local instance] realArchUnitsMeasurable realArchUnitsBorel
  complexArchUnitsMeasurable complexArchUnitsBorel
  realArchUnitsSecondCountable complexArchUnitsSecondCountable
  realArchUnitsSigmaCompact complexArchUnitsSigmaCompact

/-- The real local zeta weight on the unit group of the completed field. -/
def realArchUnitWeight (a : ℕ) (s : ℂ) (u : ℝˣ) : ℂ :=
  ((|(u : ℝ)| : ℝ) : ℂ) ^ s * (if (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1)

/-- The complex local zeta weight uses the squared radius and angular power. -/
def complexArchUnitWeight (j : ℤ) (s : ℂ) (u : ℂˣ) : ℂ :=
  ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((u : ℂ) / (‖(u : ℂ)‖ : ℂ)) ^ j

private theorem realArchUnitWeight_norm (a : ℕ) (s : ℂ) (u : ℝˣ) :
    ‖realArchUnitWeight a s u‖ = ‖(u : ℝ)‖ ^ s.re := by
  rw [realArchUnitWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr u.ne_zero),
    Real.norm_eq_abs]
  split <;> simp

private theorem complexArchUnitWeight_norm (j : ℤ) (s : ℂ) (u : ℂˣ) :
    ‖complexArchUnitWeight j s u‖ = ‖(u : ℂ)‖ ^ (2 * s.re) := by
  have hu : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr u.ne_zero
  rw [complexArchUnitWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hu 2),
    norm_zpow, norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le, div_self hu.ne',
    one_zpow, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  norm_num

private theorem realArchUnitWeight_measurable (a : ℕ) (s : ℂ) :
    Measurable (realArchUnitWeight a s) := by
  have h : Continuous (fun u : ℝˣ => ((|(u : ℝ)| : ℝ) : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Complex.continuousAt_ofReal_cpow_const |(u : ℝ)| s (Or.inr (abs_pos.mpr u.ne_zero).ne')).comp
      (f := fun u : ℝˣ => |(u : ℝ)|) Units.continuous_val.abs.continuousAt
  exact h.measurable.mul <|
    measurable_const.ite (measurableSet_lt Units.continuous_val.measurable measurable_const) measurable_const

private theorem complexArchUnitWeight_measurable (j : ℤ) (s : ℂ) :
    Measurable (complexArchUnitWeight j s) := by
  have h : Continuous (fun u : ℂˣ => ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hu : ‖(u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
    exact (Complex.continuousAt_ofReal_cpow_const (‖(u : ℂ)‖ ^ 2) s (Or.inr (pow_ne_zero 2 hu))).comp
      (f := fun u : ℂˣ => ‖(u : ℂ)‖ ^ 2) (Units.continuous_val.norm.pow 2).continuousAt
  have h' : Continuous (fun u : ℂˣ => (u : ℂ) / (‖(u : ℂ)‖ : ℂ)) :=
    Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun u => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))
  exact (h.mul (h'.zpow₀ j fun u => Or.inl
    (div_ne_zero u.ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))))).measurable

private theorem schwartz_weighted_product_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝓢(E, ℂ)) (x : E) (m : ℕ)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (hr' : ∀ i, r i ≤ ‖x‖) :
    (∏ i, max 1 (r i ^ m)) * ‖f x‖ ≤
      max (SchwartzMap.seminorm ℂ 0 0 f) (SchwartzMap.seminorm ℂ (m * Fintype.card I) 0 f) := by
  have hb : (∏ i, max 1 (r i ^ m)) ≤ ∏ _i : I, max 1 (‖x‖ ^ m) :=
    Finset.prod_le_prod (fun _ _ => zero_le_one.trans (le_max_left _ _))
      (fun i _ => max_le_max_left _ (pow_le_pow_left₀ (hr i) (hr' i) _))
  rw [Finset.prod_const, Finset.card_univ] at hb
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans
  by_cases hx : ‖x‖ ^ m ≤ 1
  · rw [max_eq_left hx, one_pow, one_mul]
    exact (SchwartzMap.norm_le_seminorm ℂ f x).trans (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hx), ← pow_mul]
    exact (SchwartzMap.norm_pow_mul_le_seminorm ℂ f _ x).trans (le_max_right _ _)

private abbrev realUnitProductMeasure (I : Type*) [Fintype I] : Measure (I → ℝˣ) :=
  Measure.pi (fun _ : I => realArchMultiplicativeHaar)

private abbrev complexUnitProductMeasure (I : Type*) [Fintype I] : Measure (I → ℂˣ) :=
  Measure.pi (fun _ : I => complexArchMultiplicativeHaar)

private abbrev mixedUnitProductMeasure (I J : Type*) [Fintype I] [Fintype J] :
    Measure ((I → ℝˣ) × (J → ℂˣ)) :=
  (realUnitProductMeasure I).prod (complexUnitProductMeasure J)

private def complexProductIntegrand {J : Type*} [Fintype J] (j : J → ℂ × ℤ)
    (s : ℂ) (f : 𝓢(J → ℂ, ℂ)) (p : J → ℂˣ) : ℂ :=
  (∏ i, complexArchUnitWeight (j i).2 (s + (j i).1) (p i)) * f (fun i => (p i : ℂ))

private def mixedProductIntegrand {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℂ × ℕ) (j : J → ℂ × ℤ) (s : ℂ)
    (f : 𝓢((I → ℝ) × (J → ℂ), ℂ)) (p : (I → ℝˣ) × (J → ℂˣ)) : ℂ :=
  ((∏ i, realArchUnitWeight (a i).2 (s + (a i).1) (p.1 i)) *
    ∏ i, complexArchUnitWeight (j i).2 (s + (j i).1) (p.2 i)) *
    f (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ))

private theorem exists_nat_above_finite {I : Type*} [Finite I] (b : I → ℝ) :
    ∃ m : ℕ, ∀ i, b i < m := by
  obtain ⟨c, hc⟩ := (Set.finite_range b).bddAbove
  obtain ⟨m, hm⟩ := exists_nat_gt c
  exact ⟨m, fun i => (hc (Set.mem_range_self i)).trans_lt hm⟩

private theorem schwartz_weighted_product_div_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝓢(E, ℂ)) (x : E) (m : ℕ)
    (r b : I → ℝ) (hr : ∀ i, 0 ≤ r i) (hr' : ∀ i, r i ≤ ‖x‖) :
    (∏ i, r i ^ b i) * ‖f x‖ ≤
      max (SchwartzMap.seminorm ℂ 0 0 f) (SchwartzMap.seminorm ℂ (m * Fintype.card I) 0 f) *
        ∏ i, r i ^ b i / max 1 (r i ^ m) := by
  let D (i : I) := max 1 (r i ^ m)
  let M (i : I) := r i ^ b i / D i
  have hn : (∏ i, r i ^ b i) = (∏ i, D i) * ∏ i, M i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [M]
    rw [mul_comm, div_mul_cancel₀ _ (zero_lt_one.trans_le (le_max_left _ _)).ne']
  rw [hn, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (schwartz_weighted_product_le f x m r hr hr')
    (Finset.prod_nonneg (fun i _ => div_nonneg (Real.rpow_nonneg (hr i) _) (zero_le_one.trans (le_max_left _ _))))

private theorem complexProductIntegrand_integrable {J : Type*} [Fintype J]
    (j : J → ℂ × ℤ) (s : ℂ) (hj : ∀ i, 0 < (s + (j i).1).re)
    (f : 𝓢(J → ℂ, ℂ)) : Integrable (complexProductIntegrand j s f) (complexUnitProductMeasure J) := by
  let b (i : J) := 2 * (s + (j i).1).re
  obtain ⟨m, hm⟩ := exists_nat_above_finite b
  let C := max (SchwartzMap.seminorm ℂ 0 0 f) (SchwartzMap.seminorm ℂ (m * Fintype.card J) 0 f)
  have hu (i : J) : Integrable (fun u : ℂˣ => ‖(u : ℂ)‖ ^ b i / max 1 (‖(u : ℂ)‖ ^ m))
      complexArchMultiplicativeHaar :=
    complexArchMultiplicativeHaar_integrable_majorant (mul_pos (by norm_num) (hj i)) (hm i)
  have hM := (Integrable.fintype_prod_dep hu).const_mul C
  have hmeas : Measurable (complexProductIntegrand j s f) := by
    apply Measurable.mul
    · exact Finset.measurable_prod _ fun i _ =>
        (complexArchUnitWeight_measurable _ _).comp (measurable_pi_apply i)
    · exact (f.continuous.comp (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i))).measurable
  apply hM.mono' hmeas.aestronglyMeasurable
  exact .of_forall fun p => by
    simp only [complexProductIntegrand, norm_mul, norm_prod, complexArchUnitWeight_norm]
    exact schwartz_weighted_product_div_le f (fun i => (p i : ℂ)) m (fun i => ‖(p i : ℂ)‖)
      b (fun _ => norm_nonneg _) (fun i => norm_le_pi_norm (fun k : J => (p k : ℂ)) i)

private theorem mixedProductIntegrand_integrable {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℂ × ℕ) (j : J → ℂ × ℤ) (s : ℂ)
    (ha : ∀ i, 0 < (s + (a i).1).re) (hj : ∀ i, 0 < (s + (j i).1).re)
    (f : 𝓢((I → ℝ) × (J → ℂ), ℂ)) :
    Integrable (mixedProductIntegrand a j s f) (mixedUnitProductMeasure I J) := by
  let bR (i : I) := (s + (a i).1).re
  let bC (i : J) := 2 * (s + (j i).1).re
  let b := Sum.elim bR bC
  obtain ⟨m, hm⟩ := exists_nat_above_finite b
  let C := max (SchwartzMap.seminorm ℂ 0 0 f)
    (SchwartzMap.seminorm ℂ (m * Fintype.card (I ⊕ J)) 0 f)
  have hR (i : I) : Integrable (fun u : ℝˣ => ‖(u : ℝ)‖ ^ bR i / max 1 (‖(u : ℝ)‖ ^ m))
      realArchMultiplicativeHaar :=
    realArchMultiplicativeHaar_integrable_majorant (ha i) (hm (.inl i))
  have hC (i : J) : Integrable (fun u : ℂˣ => ‖(u : ℂ)‖ ^ bC i / max 1 (‖(u : ℂ)‖ ^ m))
      complexArchMultiplicativeHaar :=
    complexArchMultiplicativeHaar_integrable_majorant (mul_pos (by norm_num) (hj i)) (hm (.inr i))
  have hM := ((Integrable.fintype_prod_dep hR).mul_prod (Integrable.fintype_prod_dep hC)).const_mul C
  have hmeas : Measurable (mixedProductIntegrand a j s f) := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact Finset.measurable_prod _ fun i _ =>
          (realArchUnitWeight_measurable _ _).comp ((measurable_pi_apply i).comp measurable_fst)
      · exact Finset.measurable_prod _ fun i _ =>
          (complexArchUnitWeight_measurable _ _).comp ((measurable_pi_apply i).comp measurable_snd)
    · have hvR (i : I) : Continuous (fun u : I → ℝˣ => (u i : ℝ)) :=
        (Units.continuous_val (M := ℝ)).comp (continuous_apply i)
      have hvC (i : J) : Continuous (fun u : J → ℂˣ => (u i : ℂ)) :=
        (Units.continuous_val (M := ℂ)).comp (continuous_apply i)
      have hR : Continuous (fun p : (I → ℝˣ) × (J → ℂˣ) => fun i : I => (p.1 i : ℝ)) :=
        continuous_pi fun i => (hvR i).comp continuous_fst
      have hC : Continuous (fun p : (I → ℝˣ) × (J → ℂˣ) => fun i : J => (p.2 i : ℂ)) :=
        continuous_pi fun i => (hvC i).comp continuous_snd
      exact (f.continuous.comp (hR.prodMk hC)).measurable
  apply hM.mono' hmeas.aestronglyMeasurable
  exact .of_forall fun p => by
    let x : (I → ℝ) × (J → ℂ) := (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ))
    let r := Sum.elim (fun i : I => ‖(p.1 i : ℝ)‖) (fun i : J => ‖(p.2 i : ℂ)‖)
    have hr (i : I ⊕ J) : 0 ≤ r i := by cases i <;> exact norm_nonneg _
    have hr' (i : I ⊕ J) : r i ≤ ‖x‖ := by
      rw [Prod.norm_def]
      cases i with
      | inl i => exact (norm_le_pi_norm x.1 i).trans (le_max_left _ _)
      | inr i => exact (norm_le_pi_norm x.2 i).trans (le_max_right _ _)
    have h := schwartz_weighted_product_div_le f x m r b hr hr'
    simpa only [Fintype.prod_sum_type, r, b, Sum.elim_inl, Sum.elim_inr, mixedProductIntegrand,
      norm_mul, norm_prod, realArchUnitWeight_norm, complexArchUnitWeight_norm, x, C] using h

private theorem complexPlacesZeta_eq_productIntegral (s : ℂ) :
    ∀ (n : ℕ) (j : Fin n → ℂ × ℤ), (∀ i, 0 < (s + (j i).1).re) →
      ∀ f : 𝓢(Fin n → ℂ, ℂ), complexPlacesZeta complexTamagawaAngularMeasure n j s f =
        ∫ p, complexProductIntegrand j s f p ∂complexUnitProductMeasure (Fin n)
  | 0, _, _, f => by
    have h (p : Fin 0 → ℂˣ) : (fun i => (p i : ℂ)) = 0 := Subsingleton.elim _ _
    simp [complexPlacesZeta, emptyContraction, complexProductIntegrand, h, measureReal_def]
    rfl
  | n + 1, j, hj, f => by
    let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitFinCoordinate n ℂ).symm f
    let t := complexArchimedeanZetaInFirst complexTamagawaAngularMeasure (j 0).2 (s + (j 0).1) g
    let F := complexProductIntegrand j s f
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂˣ) 0).symm
    have he : MeasurePreserving e
        (complexArchMultiplicativeHaar.prod (complexUnitProductMeasure (Fin n)))
        (complexUnitProductMeasure (Fin (n + 1))) :=
      (measurePreserving_piFinSuccAbove (fun _ => complexArchMultiplicativeHaar) 0).symm
    have hI := he.integrable_comp_of_integrable (complexProductIntegrand_integrable j s hj f)
    change complexPlacesZeta complexTamagawaAngularMeasure n (Fin.tail j) s t =
      ∫ p, F p ∂complexUnitProductMeasure (Fin (n + 1))
    rw [complexPlacesZeta_eq_productIntegral s n (Fin.tail j) (fun i => hj i.succ),
      ← he.integral_comp' F]
    erw [integral_prod_symm _ hI]
    apply integral_congr_ae
    refine .of_forall fun p => ?_
    rw [complexProductIntegrand, show t (fun i => (p i : ℂ)) =
      ∫ u, complexArchUnitWeight (j 0).2 (s + (j 0).1) u * g ((u : ℂ), fun i => (p i : ℂ))
        ∂complexArchMultiplicativeHaar from
      (complexArchimedeanZetaInFirst_eq_unitIntegral _ _ (hj 0) g _).2, ← integral_const_mul]
    apply integral_congr_ae
    refine .of_forall fun u => ?_
    simp only [Function.comp_apply, complexProductIntegrand, e,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ,
      Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.cons_zero, Fin.tail,
      g, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    rw [mul_left_comm, ← mul_assoc]
    congr 1
    apply congrArg f
    funext i
    change Fin.cons (α := fun _ => ℂ) (u : ℂ) (fun k => (p k : ℂ)) i =
      (Fin.cons (α := fun _ => ℂˣ) u p i : ℂ)
    exact Fin.cases (by simp) (fun k => by simp) i

private theorem archimedeanPlacesZeta_eq_productIntegral (m : ℕ) (j : Fin m → ℂ × ℤ)
    (s : ℂ) (hj : ∀ i, 0 < (s + (j i).1).re) :
    ∀ (n : ℕ) (a : Fin n → ℂ × ℕ), (∀ i, 0 < (s + (a i).1).re) →
      ∀ f : 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ),
        archimedeanPlacesZeta complexTamagawaAngularMeasure m j n a s f =
          ∫ p, mixedProductIntegrand a j s f p ∂mixedUnitProductMeasure (Fin n) (Fin m)
  | 0, a, ha, f => by
    rw [archimedeanPlacesZeta, ContinuousLinearMap.comp_apply, complexPlacesZeta_eq_productIntegral s m j hj,
      integral_prod_symm _ (mixedProductIntegrand_integrable a j s ha hj f)]
    apply integral_congr_ae
    refine .of_forall fun p => ?_
    have hr (q : Fin 0 → ℝˣ) : (fun i => (q i : ℝ)) = 0 := Subsingleton.elim _ _
    simp [mixedProductIntegrand, complexProductIntegrand, hr, measureReal_def, discardEmptyRealCoordinates]
    left
    change f ((0 : Fin 0 → ℝ), fun i => (p i : ℂ)) = _
    exact congrArg f (Prod.ext (Subsingleton.elim _ _) rfl)
  | n + 1, a, ha, f => by
    let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitRealCoordinate n (Fin m → ℂ)).symm f
    let t := realArchimedeanZetaInFirst (a 0).2 (s + (a 0).1) g
    let F := mixedProductIntegrand a j s f
    let e₀ := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝˣ) 0).symm
    let e := MeasurableEquiv.prodAssoc.symm.trans
      (e₀.prodCongr (MeasurableEquiv.refl (Fin m → ℂˣ)))
    have he : MeasurePreserving e
        (realArchMultiplicativeHaar.prod (mixedUnitProductMeasure (Fin n) (Fin m)))
        (mixedUnitProductMeasure (Fin (n + 1)) (Fin m)) :=
      (((measurePreserving_piFinSuccAbove (fun _ => realArchMultiplicativeHaar) 0).symm).prod
        (MeasurePreserving.id (complexUnitProductMeasure (Fin m)))).comp
        (measurePreserving_prodAssoc realArchMultiplicativeHaar (realUnitProductMeasure (Fin n))
          (complexUnitProductMeasure (Fin m))).symm
    have hI := he.integrable_comp_of_integrable (mixedProductIntegrand_integrable a j s ha hj f)
    change archimedeanPlacesZeta complexTamagawaAngularMeasure m j n (Fin.tail a) s t =
      ∫ p, F p ∂mixedUnitProductMeasure (Fin (n + 1)) (Fin m)
    rw [archimedeanPlacesZeta_eq_productIntegral m j s hj n (Fin.tail a) (fun i => ha i.succ),
      ← he.integral_comp' F]
    erw [integral_prod_symm _ hI]
    apply integral_congr_ae
    refine .of_forall fun p => ?_
    rw [mixedProductIntegrand, show t (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ)) =
      ∫ u, realArchUnitWeight (a 0).2 (s + (a 0).1) u *
        g ((u : ℝ), (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ))) ∂realArchMultiplicativeHaar from
      (realArchimedeanZetaInFirst_eq_unitIntegral _ _ (ha 0) g _).2, ← integral_const_mul]
    apply integral_congr_ae
    refine .of_forall fun u => ?_
    have hcoord : e (u, p) = (Fin.cons u p.1, p.2) := by
      refine Prod.ext ?_ ?_
      swap
      · rfl
      change e₀ (u, p.1) = Fin.cons u p.1
      simp only [e₀, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
    have hval : g ((u : ℝ), (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ))) =
        f (fun i => (Fin.cons (α := fun _ => ℝˣ) u p.1 i : ℝ), fun i => (p.2 i : ℂ)) := by
      apply congrArg f
      refine Prod.ext ?_ ?_
      swap
      · rfl
      change Fin.cons (α := fun _ => ℝ) (u : ℝ) (fun i => (p.1 i : ℝ)) =
        fun i => (Fin.cons (α := fun _ => ℝˣ) u p.1 i : ℝ)
      funext i
      exact Fin.cases (by simp) (fun k => by simp) i
    simp only [Function.comp_apply, mixedProductIntegrand, hcoord, hval, Fin.prod_univ_succ,
      Fin.cons_succ, Fin.cons_zero, Fin.tail]
    ac_rfl

variable (F : Type*) [Field F] [NumberField F]

private abbrev RealPlaces := {w : InfinitePlace F // w.IsReal}
private abbrev ComplexPlaces := {w : InfinitePlace F // w.IsComplex}

/-- Absolute convergence of the product of local archimedean zeta weights
against a Schwartz test in the common initial half-plane. -/
theorem archimedeanNumberFieldZeta_integrable_product
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (s : ℂ)
    (ha : ∀ i, 0 < (s + (a i).1).re) (hj : ∀ i, 0 < (s + (j i).1).re)
    (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    Integrable (fun p : (RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ) =>
      ((∏ i, realArchUnitWeight (a i).2 (s + (a i).1) (p.1 i)) *
        (∏ i, complexArchUnitWeight (j i).2 (s + (j i).1) (p.2 i))) *
        f (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ)))
      ((Measure.pi fun _ : RealPlaces F => realArchMultiplicativeHaar).prod
        (Measure.pi fun _ : ComplexPlaces F => complexArchMultiplicativeHaar)) :=
  mixedProductIntegrand_integrable a j s ha hj f

private def enumerateArchimedeanCoordinates :
    mixedEmbedding.mixedSpace F ≃L[ℝ]
      (Fin (Fintype.card (RealPlaces F)) → ℝ) × (Fin (Fintype.card (ComplexPlaces F)) → ℂ) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (Fintype.equivFin (RealPlaces F))).prodCongr
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℂ) (Fintype.equivFin (ComplexPlaces F)))

/-- The product continuation on the actual mixed Schwartz space of the
number field, with the local sign and circle characters supplied by place. -/
def archimedeanNumberFieldZeta (ν : Measure Circle) [IsFiniteMeasure ν]
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (s : ℂ) :
    𝓢(mixedEmbedding.mixedSpace F, ℂ) →L[ℂ] ℂ :=
  (archimedeanPlacesZeta ν _ (j ∘ (Fintype.equivFin (ComplexPlaces F)).symm)
    _ (a ∘ (Fintype.equivFin (RealPlaces F)).symm) s).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (enumerateArchimedeanCoordinates F).symm)

/-- Uniform strip estimate for the joint archimedean continuation of
a number field, with no product assumption on the test. -/
theorem archimedeanNumberFieldZeta_uniform_seminorm (ν : Measure Circle) [IsFiniteMeasure ν]
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (l r : ℝ) :
    ∃ p : Seminorm ℂ 𝓢(mixedEmbedding.mixedSpace F, ℂ), Continuous p ∧
      ∀ (s : ℂ), s.re ∈ Icc l r → (∀ i, 1 ≤ |(s + (j i).1).im|) →
        (∀ i, 1 ≤ |(s + (a i).1).im|) → ∀ f, ‖archimedeanNumberFieldZeta F ν a j s f‖ ≤ p f := by
  obtain ⟨p, hp, hbound⟩ := archimedeanPlacesZeta_uniform_seminorm ν l r _
    (j ∘ (Fintype.equivFin (ComplexPlaces F)).symm) _ (a ∘ (Fintype.equivFin (RealPlaces F)).symm)
  let T := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ (enumerateArchimedeanCoordinates F).symm
  exact ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun s hs hj ha f ↦
    hbound s hs (fun i ↦ hj ((Fintype.equivFin (ComplexPlaces F)).symm i))
      (fun i ↦ ha ((Fintype.equivFin (RealPlaces F)).symm i)) (T f)⟩

/-- The joint archimedean continuation agrees with the Haar product integral on
the common initial half-plane, for a Schwartz test coupling all places. -/
theorem archimedeanNumberFieldZeta_eq_productIntegral
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (s : ℂ)
    (ha : ∀ i, 0 < (s + (a i).1).re) (hj : ∀ i, 0 < (s + (j i).1).re)
    (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j s f =
      ∫ p : (RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ),
        ((∏ i, realArchUnitWeight (a i).2 (s + (a i).1) (p.1 i)) *
          (∏ i, complexArchUnitWeight (j i).2 (s + (j i).1) (p.2 i))) *
          f (fun i => (p.1 i : ℝ), fun i => (p.2 i : ℂ)) ∂archimedeanCoordinateMeasure F := by
  let er := Fintype.equivFin (RealPlaces F)
  let ec := Fintype.equivFin (ComplexPlaces F)
  let e := (MeasurableEquiv.piCongrLeft (fun _ : RealPlaces F => ℝˣ) er.symm).prodCongr
    (MeasurableEquiv.piCongrLeft (fun _ : ComplexPlaces F => ℂˣ) ec.symm)
  have he : MeasurePreserving e
      (mixedUnitProductMeasure (Fin (Fintype.card (RealPlaces F))) (Fin (Fintype.card (ComplexPlaces F))))
      (archimedeanCoordinateMeasure F) :=
    (measurePreserving_piCongrLeft (fun _ => realArchMultiplicativeHaar) er.symm).prod
      (measurePreserving_piCongrLeft (fun _ => complexArchMultiplicativeHaar) ec.symm)
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (enumerateArchimedeanCoordinates F).symm f
  change archimedeanPlacesZeta complexTamagawaAngularMeasure _ (j ∘ ec.symm) _ (a ∘ er.symm) s g =
    ∫ p, mixedProductIntegrand a j s f p ∂archimedeanCoordinateMeasure F
  rw [archimedeanPlacesZeta_eq_productIntegral _ (j ∘ ec.symm) s (fun i => hj (ec.symm i)) _
    (a ∘ er.symm) (fun i => ha (er.symm i)), ← he.integral_comp' (mixedProductIntegrand a j s f)]
  apply integral_congr_ae
  refine .of_forall fun p => ?_
  have hr (i : RealPlaces F) : (e p).1 i = p.1 (er i) := by
    change MeasurableEquiv.piCongrLeft (fun _ : RealPlaces F => ℝˣ) er.symm p.1 i = _
    simpa only [Equiv.symm_apply_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝˣ) er.symm p.1 (er i))
  have hc (i : ComplexPlaces F) : (e p).2 i = p.2 (ec i) := by
    change MeasurableEquiv.piCongrLeft (fun _ : ComplexPlaces F => ℂˣ) ec.symm p.2 i = _
    simpa only [Equiv.symm_apply_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂˣ) ec.symm p.2 (ec i))
  simp only [mixedProductIntegrand, Function.comp_apply, hr, hc]
  rw [← er.symm.prod_comp (fun i => realArchUnitWeight (a i).2 (s + (a i).1) (p.1 (er i))),
    ← ec.symm.prod_comp (fun i => complexArchUnitWeight (j i).2 (s + (j i).1) (p.2 (ec i)))]
  simp only [Equiv.apply_symm_apply, g, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rfl

/-- Away from the actual one-place pole lattices the full archimedean
operator is differentiated with a quadratic remainder in Schwartz seminorms. -/
theorem archimedeanNumberFieldZeta_hasOperatorTaylorEstimate
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (c : ℂ)
    (ha : ∀ i, RealArchZetaRegular (a i).2 (c + (a i).1))
    (hj : ∀ i, ComplexArchZetaRegular (j i).2 (c + (j i).1)) :
    ∃ D, HasOperatorTaylorEstimate (archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j) c D := by
  obtain ⟨D, h⟩ := archimedeanPlacesZeta_hasOperatorTaylorEstimate
    _ (j ∘ (Fintype.equivFin (ComplexPlaces F)).symm) c (fun i => hj _)
    _ (a ∘ (Fintype.equivFin (RealPlaces F)).symm) (fun i => ha _)
  exact ⟨_, h.comp (HasOperatorTaylorEstimate.const _ c)⟩

/-- The entire reciprocal of the product of the archimedean Euler factors. -/
def archimedeanNumberFieldZetaDenominator (a : RealPlaces F → ℂ × ℕ)
    (j : ComplexPlaces F → ℂ × ℤ) (z : ℂ) : ℂ :=
  (∏ i, realArchZetaDenominator (a i).2 (z + (a i).1)) *
  (∏ i, complexArchZetaDenominator (j i).2 (z + (j i).1))

theorem archimedeanNumberFieldZetaDenominator_analytic (a : RealPlaces F → ℂ × ℕ)
    (j : ComplexPlaces F → ℂ × ℤ) (c : ℂ) :
    AnalyticAt ℂ (archimedeanNumberFieldZetaDenominator F a j) c := by
  apply AnalyticAt.mul
  · exact Finset.analyticAt_fun_prod _ fun i _ =>
      (realArchZetaDenominator_analytic (a i).2 (c + (a i).1)).comp
        (f := fun z : ℂ => z + (a i).1) (x := c) (analyticAt_id.add analyticAt_const)
  · exact Finset.analyticAt_fun_prod _ fun i _ =>
      (complexArchZetaDenominator_analytic (j i).2 (c + (j i).1)).comp
        (f := fun z : ℂ => z + (j i).1) (x := c) (analyticAt_id.add analyticAt_const)

theorem archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (z : ℂ)
    (ha : ∀ i, 0 < (z + (a i).1).re) (hj : ∀ i, 0 < (z + (j i).1).re) :
    archimedeanNumberFieldZetaDenominator F a j z ≠ 0 := by
  apply mul_ne_zero
  · refine Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero ?_
    apply (realArchZetaRegular_iff_gamma _ _).mp
    intro k hk
    have h := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h
    linarith [show 0 < z.re + (a i).1.re by simpa only [Complex.add_re] using ha i,
      (Nat.cast_nonneg k : 0 ≤ (k : ℝ))]
  · refine Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero ?_
    apply (complexArchZetaRegular_iff_gamma _ _).mp
    intro k hk
    have h := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.zero_re,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at h
    linarith [show 0 < z.re + (j i).1.re by simpa only [Complex.add_re] using hj i,
      (Nat.cast_nonneg k : 0 ≤ (k : ℝ))]

/-- The reciprocal Gamma product removes the archimedean poles on every
joint Schwartz test, with analytic operator germs on the full test space. -/
theorem archimedeanNumberFieldZeta_denominator_analyticOperatorGerm
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (c : ℂ) :
    AnalyticOperatorGerm (fun z =>
      archimedeanNumberFieldZetaDenominator F a j z •
        archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z) c := by
  have h := archimedeanPlacesZeta_denominator_analyticOperatorGerm
    _ (j ∘ (Fintype.equivFin (ComplexPlaces F)).symm) c
    _ (a ∘ (Fintype.equivFin (RealPlaces F)).symm)
  apply (h.smul_comp_const (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (enumerateArchimedeanCoordinates F).symm)).congr (.of_forall fun z => ?_)
  dsimp only [archimedeanNumberFieldZetaDenominator, archimedeanNumberFieldZeta, Function.comp_apply]
  rw [(Fintype.equivFin (RealPlaces F)).symm.prod_comp
      (fun i => realArchZetaDenominator (a i).2 (z + (a i).1)),
    (Fintype.equivFin (ComplexPlaces F)).symm.prod_comp
      (fun i => complexArchZetaDenominator (j i).2 (z + (j i).1))]

theorem archimedeanNumberFieldZeta_meromorphic (ν : Measure Circle) [IsFiniteMeasure ν]
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    Meromorphic (fun s => archimedeanNumberFieldZeta F ν a j s f) :=
  ((archimedeanPlacesZeta_meromorphicOperator ν _ _ _ _).comp (.const _)).apply_meromorphic f

private def complexCoordinateFlat {n : ℕ} (f : 𝓢(Fin n → ℂ, ℂ)) : Prop :=
  ∀ x : Fin n → ℂ, (∃ i, x i = 0) → ∀ k : ℕ, iteratedFDeriv ℝ k f x = 0

private def mixedCoordinateFlat {n m : ℕ} (f : 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ)) : Prop :=
  ∀ x : (Fin n → ℝ) × (Fin m → ℂ), ((∃ i, x.1 i = 0) ∨ (∃ i, x.2 i = 0)) →
    ∀ k : ℕ, iteratedFDeriv ℝ k f x = 0

private theorem exists_complexPlacesZeta_flatGerm
    (ν : Measure Circle) [IsFiniteMeasure ν] (c : ℂ) :
    ∀ (n : ℕ) (j : Fin n → ℂ × ℤ),
      ∃ A : ℂ → 𝓢(Fin n → ℂ, ℂ) →L[ℂ] ℂ, AnalyticOperatorGerm A c ∧
        ∀ᶠ z in 𝓝 c, ∀ f : 𝓢(Fin n → ℂ, ℂ), complexCoordinateFlat f →
          complexPlacesZeta ν n j z f = A z f
  | 0, _ => ⟨fun _ ↦ emptyContraction, .const _, .of_forall fun _ _ _ ↦ rfl⟩
  | n+1, j => by
    obtain ⟨A, hA, hnearA⟩ := exists_complexArchimedeanZetaInFirst_flatGerm
      (Y := Fin n → ℂ) ν (j 0).2 (c + (j 0).1)
    obtain ⟨B, hB, hnearB⟩ := exists_complexPlacesZeta_flatGerm ν c n (Fin.tail j)
    let e := (splitFinCoordinate n ℂ).symm
    let P : 𝓢(Fin (n + 1) → ℂ, ℂ) →L[ℂ] 𝓢(ℂ × (Fin n → ℂ), ℂ) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    refine ⟨fun z ↦ (B z).comp ((A (z+(j 0).1)).comp P),
      hB.comp ((hA.translate _).comp (.const P)), ?_⟩
    have hnearA' := ((continuous_id.add continuous_const : Continuous (fun z : ℂ ↦ z+(j 0).1)).tendsto c).eventually hnearA
    filter_upwards [hnearA', hnearB] with z hz hz'
    intro f hf
    have hzero (y : Fin n → ℂ) (k : ℕ) : iteratedFDeriv ℝ k (P f) (0,y) = 0 := by
      apply schwartzLinearPullback_jet_zero e.toContinuousLinearMap f
      apply hf (e (0,y)) _ k
      refine ⟨0, ?_⟩
      change Fin.cons (α := fun _ : Fin (n+1) ↦ ℂ) 0 y 0 = 0
      rw [Fin.cons_zero]
    have hflat : complexCoordinateFlat (A (z+(j 0).1) (P f)) := by
      intro y hy k
      apply hz.2 (P f) y _ k
      intro t l
      apply schwartzLinearPullback_jet_zero e.toContinuousLinearMap f
      obtain ⟨i, hi⟩ := hy
      apply hf (e (t,y)) _ l
      refine ⟨i.succ, ?_⟩
      change Fin.cons (α := fun _ : Fin (n+1) ↦ ℂ) t y i.succ = 0
      rwa [Fin.cons_succ]
    change complexPlacesZeta ν n (Fin.tail j) z
      (complexArchimedeanZetaInFirst ν (j 0).2 (z+(j 0).1) (P f)) = B z (A (z+(j 0).1) (P f))
    have hEq : complexArchimedeanZetaInFirst ν (j 0).2 (z+(j 0).1) (P f) =
        A (z+(j 0).1) (P f) := hz.1 (P f) hzero
    rw [hEq, hz' _ hflat]

private theorem exists_archimedeanPlacesZeta_flatGerm
    (ν : Measure Circle) [IsFiniteMeasure ν] (m : ℕ) (j : Fin m → ℂ × ℤ) (c : ℂ) :
    ∀ (n : ℕ) (a : Fin n → ℂ × ℕ),
      ∃ A : ℂ → 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ) →L[ℂ] ℂ, AnalyticOperatorGerm A c ∧
        ∀ᶠ z in 𝓝 c, ∀ f : 𝓢((Fin n → ℝ) × (Fin m → ℂ), ℂ), mixedCoordinateFlat f →
          archimedeanPlacesZeta ν m j n a z f = A z f
  | 0, _ => by
    obtain ⟨A, hA, hnear⟩ := exists_complexPlacesZeta_flatGerm ν c m j
    let P := discardEmptyRealCoordinates (Fin m → ℂ)
    refine ⟨fun z ↦ (A z).comp P, hA.comp (.const P), ?_⟩
    filter_upwards [hnear] with z hz
    intro f hf
    change complexPlacesZeta ν m j z (P f) = A z (P f)
    apply hz
    intro x hx k
    apply schwartzLinearPullback_jet_zero (ContinuousLinearMap.inr ℝ (Fin 0 → ℝ) (Fin m → ℂ)) f
    exact hf (0,x) (Or.inr hx) k
  | n+1, a => by
    obtain ⟨A, hA, hnearA⟩ := exists_realArchimedeanZetaInFirst_flatGerm
      (Y := (Fin n → ℝ) × (Fin m → ℂ)) (a 0).2 (c+(a 0).1)
    obtain ⟨B, hB, hnearB⟩ := exists_archimedeanPlacesZeta_flatGerm ν m j c n (Fin.tail a)
    let e := (splitRealCoordinate n (Fin m → ℂ)).symm
    let P : 𝓢((Fin (n + 1) → ℝ) × (Fin m → ℂ), ℂ) →L[ℂ]
        𝓢(ℝ × (Fin n → ℝ) × (Fin m → ℂ), ℂ) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    refine ⟨fun z ↦ (B z).comp ((A (z+(a 0).1)).comp P),
      hB.comp ((hA.translate _).comp (.const P)), ?_⟩
    have hnearA' := ((continuous_id.add continuous_const : Continuous (fun z : ℂ ↦ z+(a 0).1)).tendsto c).eventually hnearA
    filter_upwards [hnearA', hnearB] with z hz hz'
    intro f hf
    have hzero (y : (Fin n → ℝ) × (Fin m → ℂ)) (k : ℕ) :
        iteratedFDeriv ℝ k (P f) (0,y) = 0 := by
      apply schwartzLinearPullback_jet_zero e.toContinuousLinearMap f
      apply hf (e (0,y)) _ k
      refine Or.inl ⟨0, ?_⟩
      change Fin.cons (α := fun _ : Fin (n+1) ↦ ℝ) 0 y.1 0 = 0
      rw [Fin.cons_zero]
    have hflat : mixedCoordinateFlat (A (z+(a 0).1) (P f)) := by
      intro y hy k
      apply hz.2 (P f) y _ k
      intro t l
      apply schwartzLinearPullback_jet_zero e.toContinuousLinearMap f
      apply hf
      rcases hy with ⟨i, hi⟩ | h
      · refine Or.inl ⟨i.succ, ?_⟩
        change Fin.cons (α := fun _ : Fin (n+1) ↦ ℝ) t y.1 i.succ = 0
        rwa [Fin.cons_succ]
      · exact Or.inr h
    change archimedeanPlacesZeta ν m j n (Fin.tail a) z
      (realArchimedeanZetaInFirst (a 0).2 (z+(a 0).1) (P f)) = B z (A (z+(a 0).1) (P f))
    have hEq : realArchimedeanZetaInFirst (a 0).2 (z+(a 0).1) (P f) =
        A (z+(a 0).1) (P f) := hz.1 (P f) hzero
    rw [hEq, hz' _ hflat]

/-- The simultaneous archimedean continuation has a holomorphic germ at
every parameter when the joint test is flat on each coordinate hyperplane. -/
theorem archimedeanNumberFieldZeta_exists_analyticGerm_of_flat
    (ν : Measure Circle) [IsFiniteMeasure ν]
    (a : RealPlaces F → ℂ × ℕ) (j : ComplexPlaces F → ℂ × ℤ)
    (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (hf : ∀ x : mixedEmbedding.mixedSpace F,
      ((∃ v : RealPlaces F, x.1 v = 0) ∨ (∃ v : ComplexPlaces F, x.2 v = 0)) →
        ∀ k : ℕ, iteratedFDeriv ℝ k f x = 0) (c : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      (fun z ↦ archimedeanNumberFieldZeta F ν a j z f) =ᶠ[𝓝[≠] c] g := by
  let er := Fintype.equivFin (RealPlaces F)
  let ec := Fintype.equivFin (ComplexPlaces F)
  let e := (enumerateArchimedeanCoordinates F).symm
  let f' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hflat : mixedCoordinateFlat f' := by
    intro x hx k
    apply schwartzLinearPullback_jet_zero e.toContinuousLinearMap f
    apply hf
    rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨er.symm i, by change x.1 (er (er.symm i)) = 0; rwa [er.apply_symm_apply]⟩
    · exact Or.inr ⟨ec.symm i, by change x.2 (ec (ec.symm i)) = 0; rwa [ec.apply_symm_apply]⟩
  obtain ⟨A, hA, he⟩ := exists_archimedeanPlacesZeta_flatGerm ν _ (j ∘ ec.symm) c _ (a ∘ er.symm)
  obtain ⟨g, hg, hAf⟩ := hA.apply_exists_analytic f'
  refine ⟨g, hg, ?_⟩
  apply EventuallyEq.trans _ hAf
  exact (he.filter_mono nhdsWithin_le_nhds).mono (fun _ hz ↦ hz f' hflat)

end

end Masullo
