import ElementarySchwartzSymbols
import ElementarySchwartzNuclear
import IntegratedDerivativeCube
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F] [MeasurableSpace F] [BorelSpace F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => ElementarySchwartz m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "Directions" => List (Multiplicative ℝ →ₜ* Multiplicative A)
local notation "DualDirections" => List (Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative A))

/-- Product normalization in elementary coordinates. The unit circles have
mass one and the integer and finite factors carry counting measure. -/
def elementaryProductHaar (m n r : ℕ) (F : Type*) [MeasurableSpace F] :
    Measure (ElementaryLCAModel m n r F) :=
  (volume : Measure (EuclideanSpace ℝ (Fin m))).prod
    ((volume : Measure (Fin n → AddCircle (1 : ℝ))).prod
      ((Measure.count : Measure (Fin r → ℤ)).prod (Measure.count : Measure F)))

local notation "μ" => elementaryProductHaar m n r F

private def elementaryDecayWeight (g : A) : ℝ :=
  (∏ i, (1 + (g.1 i)^2)⁻¹) * ∏ j, (1 + (g.2.2.1 j : ℝ)^2)⁻¹

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [MeasurableSpace F] [BorelSpace F] in
private theorem elementaryDecayWeight_pos (g : A) : 0 < elementaryDecayWeight g :=
  mul_pos (Finset.prod_pos fun _ _ => by positivity) (Finset.prod_pos fun _ _ => by positivity)

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [MeasurableSpace F] [BorelSpace F] in
private theorem elementaryDecayWeight_le_one (g : A) : elementaryDecayWeight g ≤ 1 := by
  have h (x : ℝ) : (1 + x ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg x))
  exact mul_le_one₀ (Finset.prod_le_one (fun _ _ => by positivity) (fun i _ => h (g.1 i)))
    (Finset.prod_nonneg fun _ _ => by positivity)
    (Finset.prod_le_one (fun _ _ => by positivity) (fun j _ => h (g.2.2.1 j)))

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [BorelSpace F] in
private theorem elementaryDecayWeight_integrable :
    Integrable (elementaryDecayWeight (m := m) (n := n) (r := r) (F := F)) μ := by
  have hR : Integrable (fun x : EuclideanSpace ℝ (Fin m) => ∏ i, (1 + (x i)^2)⁻¹) volume := by
    exact (PiLp.volume_preserving_ofLp (Fin m)).integrable_comp_of_integrable
      (Integrable.fintype_prod fun _ : Fin m => integrable_inv_one_add_sq)
  have hZ : Integrable (fun a : Fin r → ℤ => ∏ j, (1 + (a j : ℝ)^2)⁻¹) Measure.count := by
    apply integrable_count_iff.mpr
    apply (summable_lattice_product (J := Fin r)).congr
    intro a
    exact (Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)).symm
  have hF : Integrable (fun _ : F => (1 : ℝ)) Measure.count := integrable_const _
  have hT : Integrable (fun _ : Fin n → AddCircle (1 : ℝ) => (1 : ℝ)) volume := integrable_const _
  change Integrable
    (fun g : A => (∏ i, (1 + (g.1 i)^2)⁻¹) * ∏ j, (1 + (g.2.2.1 j : ℝ)^2)⁻¹) μ
  unfold elementaryProductHaar
  simpa only [mul_one, one_mul] using hR.mul_prod (hT.mul_prod (hZ.mul_prod hF))

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [BorelSpace F] in
private theorem elementaryDecayWeight_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp (elementaryDecayWeight (m := m) (n := n) (r := r) (F := F)) p μ := by
  let w : A → ℝ := elementaryDecayWeight
  have hi : Integrable w μ := elementaryDecayWeight_integrable
  by_cases htop : p = (⊤ : ℝ≥0∞)
  · subst p
    apply memLp_top_of_bound hi.aestronglyMeasurable 1
    exact Eventually.of_forall fun x => (Real.norm_of_nonneg (elementaryDecayWeight_pos x).le).trans_le
      (elementaryDecayWeight_le_one x)
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  apply (integrable_norm_rpow_iff hi.aestronglyMeasurable hp₀ htop).mp
  apply hi.mono' ((Real.continuous_rpow_const ENNReal.toReal_nonneg).comp_aestronglyMeasurable
    hi.aestronglyMeasurable.norm)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.norm_of_nonneg (elementaryDecayWeight_pos x).le]
  exact Real.rpow_le_self_of_le_one (elementaryDecayWeight_pos x).le
    (elementaryDecayWeight_le_one x) (by exact_mod_cast ENNReal.toReal_mono htop hp)

private def elementaryDecayPolynomial : MvPolynomial (Fin m ⊕ Fin r) ℂ :=
  ∏ j, (1 + MvPolynomial.X j ^ 2)

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [MeasurableSpace F] [BorelSpace F] in
private theorem elementaryDecayWeight_mul_polynomial (g : A) :
    elementaryDecayWeight g * ‖MvPolynomial.eval (elementaryGrowthVariables g)
      (elementaryDecayPolynomial (m := m) (r := r))‖ = 1 := by
  rw [elementaryDecayPolynomial, map_prod, norm_prod, Fintype.prod_sum_type]
  have h (x : ℝ) : ‖(1 : ℂ) + (x : ℂ)^2‖ = 1 + x^2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  simp only [map_add, map_one, map_pow, MvPolynomial.eval_X, elementaryGrowthVariables, Sum.elim_inl,
    Sum.elim_inr, ← Complex.ofReal_intCast, h]
  unfold elementaryDecayWeight
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← mul_inv]
  exact inv_mul_cancel₀ (by positivity)

omit [MeasurableSpace F] [BorelSpace F] in
private theorem elementarySchwartz_weightedWord_decay_bound (cs : Directions) (ds : DualDirections) :
    ∃ Q : Seminorm ℂ E, Continuous Q ∧ ∀ (f : E) g,
      ‖elementarySchwartz_weightedWord cs ds f g‖ ≤ Q f * elementaryDecayWeight g := by
  obtain ⟨P, hP⟩ := elementaryDualWord_polynomial ds
  obtain ⟨Q, hQ, hb⟩ := elementary_polynomialWord_bound cs (elementaryDecayPolynomial * P)
  refine ⟨Q, hQ, fun f g => ?_⟩
  have h := hb f g
  rw [map_mul, mul_assoc, norm_mul, ← hP, ← elementarySchwartz_weightedWord_apply] at h
  calc
    _ = elementaryDecayWeight g *
        (‖MvPolynomial.eval (elementaryGrowthVariables g) elementaryDecayPolynomial‖ *
          ‖elementarySchwartz_weightedWord cs ds f g‖) := by
      rw [← mul_assoc, elementaryDecayWeight_mul_polynomial, one_mul]
    _ ≤ _ := by
      rw [mul_comm (Q f)]
      exact mul_le_mul_of_nonneg_left h (elementaryDecayWeight_pos g).le

/-- Each weighted invariant word belongs to every Lᵖ with p ≥ 1, and its
Lᵖ norm is bounded by a continuous Schwartz seminorm. -/
theorem elementarySchwartz_weightedWord_memLp_bound (cs : Directions) (ds : DualDirections)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ Q : Seminorm ℂ E, Continuous Q ∧ ∀ f : E,
      MemLp (elementarySchwartz_weightedWord cs ds f) p μ ∧
      lpNorm (elementarySchwartz_weightedWord cs ds f) p μ ≤ Q f := by
  obtain ⟨Q, hQ, h⟩ := elementarySchwartz_weightedWord_decay_bound cs ds
  let w : A → ℝ := elementaryDecayWeight
  have hw : MemLp w p μ := elementaryDecayWeight_memLp hp
  refine ⟨‖lpNorm w p μ‖₊ • Q, hQ.const_smul _, fun f => ⟨?_, ?_⟩⟩
  · exact ((hw.const_smul (Q f)).mono'
      (elementarySchwartz_weightedWord cs ds f).continuous.aestronglyMeasurable
      (Eventually.of_forall (h f)))
  · calc
      _ ≤ lpNorm ((Q f) • w) p μ :=
        lpNorm_mono_real (hw.const_smul (Q f)) (h f)
      _ = (‖lpNorm w p μ‖₊ • Q) f := by
        rw [lpNorm_const_smul]
        change ‖Q f‖ * lpNorm w p μ = ‖lpNorm w p μ‖ * Q f
        rw [Real.norm_of_nonneg (apply_nonneg Q f), Real.norm_of_nonneg lpNorm_nonneg, mul_comm]

private theorem elementarySchwartz_weightedWord_memLp (cs : Directions) (ds : DualDirections)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : E) :
    MemLp (elementarySchwartz_weightedWord cs ds f) p μ :=
  ((elementarySchwartz_weightedWord_memLp_bound cs ds hp).choose_spec.2 f).1

/-- The actual weighted invariant derivative as a continuous linear map to Lᵖ. -/
def elementarySchwartz_weightedWordLp (cs : Directions) (ds : DualDirections)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : E →L[ℂ] Lp ℂ p μ := by
  let h (f : E) := elementarySchwartz_weightedWord_memLp cs ds (Fact.out : 1 ≤ p) f
  let D := elementarySchwartz_weightedWord cs ds
  let L : E →ₗ[ℂ] Lp ℂ p μ :=
    { toFun := fun f => (h f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add (h f) (h g)]
        exact (h (f + g)).toLp_congr _ (Eventually.of_forall fun x => by
          change D (f + g) x = D f x + D g x
          rw [map_add, BoundedContinuousFunction.add_apply])
      map_smul' := fun z f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul z (h f)]
        exact (h (z • f)).toLp_congr _ (Eventually.of_forall fun x => by
          change D (z • f) x = z • D f x
          rw [map_smul, BoundedContinuousFunction.smul_apply]) }
  refine ⟨L, continuous_of_continuousAt_zero L ?_⟩
  obtain ⟨Q, hQ, hbound⟩ := elementarySchwartz_weightedWord_memLp_bound cs ds (Fact.out : 1 ≤ p)
  have hb (f : E) : ‖L f‖ ≤ Q f := by
    change ‖(h f).toLp _‖ ≤ Q f
    rw [Lp.norm_toLp _ (h f), toReal_eLpNorm (h f).aestronglyMeasurable]
    exact (hbound f).2
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun f => norm_nonneg (L f)) hb (map_zero Q ▸ hQ.tendsto 0)

theorem elementarySchwartz_weightedWordLp_ae (cs : Directions) (ds : DualDirections)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : E) :
    ⇑(elementarySchwartz_weightedWordLp cs ds p f) =ᵐ[μ]
      elementarySchwartz_weightedWord cs ds f :=
  (elementarySchwartz_weightedWord_memLp cs ds Fact.out f).coeFn_toLp

theorem elementarySchwartz_weightedWordLp_norm (cs : Directions) (ds : DualDirections)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : E) :
    ‖elementarySchwartz_weightedWordLp cs ds p f‖ =
      lpNorm (elementarySchwartz_weightedWord cs ds f) p μ := by
  let h := elementarySchwartz_weightedWord_memLp cs ds (Fact.out : 1 ≤ p) f
  change ‖h.toLp _‖ = _
  rw [Lp.norm_toLp _ h, toReal_eLpNorm h.aestronglyMeasurable]


local notation "Operators" => List (ℂ × Directions)
local notation "DualOperators" => List (ℂ × DualDirections)

/-- A pair of invariant differential polynomials acts continuously into Lᵖ. -/
def elementarySchwartz_weightedOperatorLp (P : Operators) (Q : DualOperators)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : E →L[ℂ] Lp ℂ p μ :=
  (Q.map fun (d, ds) => d • (P.map fun (c, cs) =>
    c • elementarySchwartz_weightedWordLp cs ds p).sum).sum

theorem elementarySchwartz_weightedOperatorLp_ae (P : Operators) (Q : DualOperators)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : E) :
    ⇑(elementarySchwartz_weightedOperatorLp P Q p f) =ᵐ[μ]
      elementarySchwartz_weightedOperator P Q f := by
  have hadd {u v : Lp ℂ p μ} {U V : BoundedContinuousFunction A ℂ}
      (hu : ⇑u =ᵐ[μ] U) (hv : ⇑v =ᵐ[μ] V) :
      ⇑(u + v) =ᵐ[μ] (U + V : BoundedContinuousFunction A ℂ) := by
    filter_upwards [Lp.coeFn_add u v, hu, hv] with x h hx hy
    rw [h, Pi.add_apply, BoundedContinuousFunction.add_apply, hx, hy]
  have hsmul (z : ℂ) {u : Lp ℂ p μ} {U : BoundedContinuousFunction A ℂ}
      (hu : ⇑u =ᵐ[μ] U) : ⇑(z • u) =ᵐ[μ] (z • U : BoundedContinuousFunction A ℂ) := by
    filter_upwards [Lp.coeFn_smul z u, hu] with x h hx
    rw [h, Pi.smul_apply, BoundedContinuousFunction.smul_apply, hx]
  have hP (ds : DualDirections) :
      ⇑(((P.map fun (c, cs) => c • elementarySchwartz_weightedWordLp cs ds p).sum :
        E →L[ℂ] Lp ℂ p μ) f) =ᵐ[μ]
        ((P.map fun (c, cs) => c • elementarySchwartz_weightedWord cs ds).sum :
          E →L[ℂ] BoundedContinuousFunction A ℂ) f := by
    induction P with
    | nil => simpa only [List.map_nil, List.sum_nil, zero_apply,
        BoundedContinuousFunction.coe_zero] using (Lp.coeFn_zero ℂ p μ)
    | cons x P ih =>
      rcases x with ⟨z, cs⟩
      simp only [List.map_cons, List.sum_cons, add_apply, smul_apply]
      exact hadd (hsmul z (elementarySchwartz_weightedWordLp_ae cs ds p f)) ih
  unfold elementarySchwartz_weightedOperatorLp elementarySchwartz_weightedOperator
  induction Q with
  | nil => simpa only [List.map_nil, List.sum_nil, zero_apply,
      BoundedContinuousFunction.coe_zero] using (Lp.coeFn_zero ℂ p μ)
  | cons x Q ih =>
    rcases x with ⟨z, ds⟩
    simp only [List.map_cons, List.sum_cons, add_apply, smul_apply]
    exact hadd (hsmul z (hP ds)) ih

theorem elementarySchwartz_weightedOperatorLp_norm (P : Operators) (Q : DualOperators)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : E) :
    ‖elementarySchwartz_weightedOperatorLp P Q p f‖ =
      lpNorm (elementarySchwartz_weightedOperator P Q f) p μ := by
  have h := elementarySchwartz_weightedOperatorLp_ae P Q p f
  have hm := (Lp.memLp _).ae_eq h
  rw [Lp.norm_def, eLpNorm_congr_ae h, toReal_eLpNorm hm.aestronglyMeasurable]

theorem elementarySchwartz_weightedOperator_memLp (P : Operators) (Q : DualOperators)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : E) :
    MemLp (elementarySchwartz_weightedOperator P Q f) p μ :=
  (Lp.memLp _).ae_eq (elementarySchwartz_weightedOperatorLp_ae P Q p f)


private abbrev ElementaryProductCoordinates (m n r : ℕ) (F : Type*) :=
  ((Fin m → ℝ) × (Fin n → AddCircle (1 : ℝ))) × (Fin r → ℤ) × F

private def elementaryCoordinateMeasure (m n r : ℕ) (F : Type*) [MeasurableSpace F] :
    Measure (ElementaryProductCoordinates m n r F) :=
  ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin n → AddCircle (1 : ℝ)))).prod
    ((Measure.count : Measure (Fin r → ℤ)).prod (Measure.count : Measure F))

private def elementaryMeasureEquiv (m n r : ℕ) (F : Type*) [MeasurableSpace F] :
    ElementaryProductCoordinates m n r F ≃ᵐ ElementaryLCAModel m n r F :=
  (((MeasurableEquiv.toLp 2 (Fin m → ℝ)).prodCongr
    (MeasurableEquiv.refl (Fin n → AddCircle (1 : ℝ)))).prodCongr
    (MeasurableEquiv.refl ((Fin r → ℤ) × F))).trans MeasurableEquiv.prodAssoc

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [BorelSpace F] in
private theorem elementaryMeasureEquiv_measurePreserving :
    MeasurePreserving (elementaryMeasureEquiv m n r F) (elementaryCoordinateMeasure m n r F) μ := by
  let ν := (Measure.count : Measure (Fin r → ℤ)).prod (Measure.count : Measure F)
  exact (measurePreserving_prodAssoc (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (volume : Measure (Fin n → AddCircle (1 : ℝ))) ν).comp
    (((PiLp.volume_preserving_toLp (Fin m)).prod (MeasurePreserving.id _)).prod
      (MeasurePreserving.id ν))

/-- Assemble the real and covering torus coordinates of an elementary cube. -/
def elementaryCubeLinear (m n : ℕ) : (Fin (m + n) → ℝ) →L[ℝ]
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  let R := ContinuousLinearMap.pi (fun i : Fin m => ContinuousLinearMap.proj
    (R := ℝ) (φ := fun _ : Fin (m + n) => ℝ) (Fin.castAdd n i))
  let T := ContinuousLinearMap.pi (fun j : Fin n => ContinuousLinearMap.proj
    (R := ℝ) (φ := fun _ : Fin (m + n) => ℝ) (Fin.natAdd m j))
  (((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap).comp R).prod
    (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap).comp T)

private theorem elementaryCubeLinear_surjective (m n : ℕ) :
    Surjective (elementaryCubeLinear m n) := by
  rintro ⟨x, y⟩
  refine ⟨Fin.addCases (fun i => x i) (fun j => y j), ?_⟩
  apply Prod.ext
  · ext i
    change Fin.addCases (fun i => x i) (fun j => y j) (Fin.castAdd n i) = x i
    exact Fin.addCases_left i
  · ext j
    change Fin.addCases (fun i => x i) (fun j => y j) (Fin.natAdd m j) = y j
    exact Fin.addCases_right j

omit [AddCommGroup F] in
/-- The image of a translated cube in a fixed discrete fibre is dominated by
the full elementary product measure. -/
theorem elementaryCover_map_cube_le (x : X) (a : Fin r → ℤ) (b : F) :
    Measure.map (fun u => elementaryCover (x + elementaryCubeLinear m n u) a b)
      (unitDerivativeCube (m + n)) ≤ μ := by
  obtain ⟨w, rfl⟩ := elementaryCubeLinear_surjective m n x
  let e := elementaryMeasureEquiv m n r F
  let T (u : Fin (m + n) → ℝ) := (realTorusProjection (m := m) (n := n) (w + u), (a, b))
  have hT : Measurable T :=
    (realTorusProjection_measurable.comp (continuous_const.add continuous_id).measurable).prodMk
      measurable_const
  have hD : Measure.dirac (a, b) ≤ (Measure.count : Measure (Fin r → ℤ)).prod Measure.count := by
    rw [← Measure.dirac_prod_dirac]
    exact Measure.prod_mono (dirac_le_count a) (dirac_le_count b)
  have hmap : Measure.map T (unitDerivativeCube (m + n)) ≤ elementaryCoordinateMeasure m n r F :=
    realTorusProjection_map_cube_discrete_le (m := m) (n := n) w (a, b) hD
  have he : (fun u => elementaryCover (elementaryCubeLinear m n w + elementaryCubeLinear m n u)
      a b) = e ∘ T := by
    funext u
    rw [← map_add]
    rfl
  rw [he, ← Measure.map_map e.measurable hT]
  exact (Measure.map_mono hmap e.measurable).trans_eq elementaryMeasureEquiv_measurePreserving.map_eq

omit [MeasurableSpace F] [BorelSpace F] in
private theorem listDerivative_elementaryCover (f : E) (a : Fin r → ℤ) (b : F)
    (v : List X) (x : X) :
    listDerivative (fun u => f (elementaryCover u a b)) v x =
      elementaryOrbitWord (v.map elementaryOneParameter) f (elementaryCover x a b) := by
  have h := elementaryOrbitWord_tuple (fun i => elementaryOneParameter (v.get i))
    v.get (fun _ _ => rfl) f a b (f.property.1 a b) x
  have he : List.ofFn (fun i => elementaryOneParameter (r := r) (F := F) (v.get i)) =
      v.map elementaryOneParameter := by
    change List.ofFn (elementaryOneParameter (r := r) (F := F) ∘ v.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [he] at h
  exact h.symm

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] [BorelSpace F] in
private theorem elementaryCover_cube_measurable (x : X) (a : Fin r → ℤ) (b : F) :
    Measurable (fun u => elementaryCover (x + elementaryCubeLinear m n u) a b) := by
  have hX : Continuous (fun u : Fin (m + n) → ℝ => x + elementaryCubeLinear m n u) :=
    continuous_const.add (elementaryCubeLinear m n).continuous
  have ht : Measurable (fun (u : Fin (m + n) → ℝ) (i : Fin n) =>
      (((x + elementaryCubeLinear m n u).2 i : ℝ) : AddCircle (1 : ℝ))) :=
    measurable_pi_lambda _ fun i => AddCircle.measurable_mk'.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp hX.snd).measurable
  exact hX.fst.measurable.prodMk (ht.prodMk (measurable_const (a := (a, b))))

/-- A covering derivative at any point of the elementary group is bounded by
the global Lᵖ norms of finitely many invariant derivative words. -/
theorem elementaryCover_derivative_lpNorm_bound (f : E) (a : Fin r → ℤ) (b : F)
    (v : List X) (x : X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖listDerivative (fun u => f (elementaryCover u a b)) v x‖ ≤
      ((cubeMixedPartials (m + n)).map fun l =>
        lpNorm (elementarySchwartz_weightedWord
          ((l.map (fun j => elementaryCubeLinear m n (Pi.single j 1)) ++ v).map
            elementaryOneParameter) [] f) p μ).sum := by
  let T (u : Fin (m + n) → ℝ) := elementaryCover (x + elementaryCubeLinear m n u) a b
  have hT : Measurable T := elementaryCover_cube_measurable x a b
  refine (norm_listDerivative_le_integral_affineCube
    (elementaryCubeLinear m n) x (f.property.1 a b) v).trans ?_
  apply List.sum_le_sum
  intro l _
  let D := (l.map (fun j => elementaryCubeLinear m n (Pi.single j 1)) ++ v).map
    (elementaryOneParameter (r := r) (F := F))
  have hL := elementarySchwartz_weightedWord_memLp D [] (Fact.out : 1 ≤ p) f
  have hI := integral_norm_cube_le_lpNorm_of_map_le hT
    (elementaryCover_map_cube_le x a b) (Fact.out : 1 ≤ p) hL
  change (∫ u, ‖listDerivative (fun y => f (elementaryCover y a b))
    (l.map (fun j => elementaryCubeLinear m n (Pi.single j 1)) ++ v)
    (x + elementaryCubeLinear m n u)‖ ∂unitDerivativeCube (m + n)) ≤ _
  simp only [listDerivative_elementaryCover]
  simpa only [T, elementarySchwartz_weightedWord_apply, elementaryDualWord, List.map_nil,
    List.prod_nil, one_mul] using hI


private def windowPolynomial (α : Fin m → ℕ) (δ : Fin r → ℕ) :
    MvPolynomial (Fin m ⊕ Fin r) ℂ :=
  ∏ i, (2 * (1 + MvPolynomial.X i ^ 2)) ^ Sum.elim α δ i

private theorem abs_le_shifted_quadratic (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |x| ≤ 2 * (1 + (x + t)^2) := by
  calc
    |x| = |(x + t) - t| := by rw [add_sub_cancel_right]
    _ ≤ |x + t| + |t| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg ht.1]
      nlinarith [sq_nonneg (|x + t| - 1 / 2), sq_abs (x + t), ht.2]

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [MeasurableSpace F] [BorelSpace F] in
private theorem monomial_le_windowPolynomial (α : Fin m → ℕ) (δ : Fin r → ℕ)
    (x : X) (a : Fin r → ℤ) (b : F) (u : Fin (m + n) → ℝ)
    (hu : ∀ j, u j ∈ Icc (0 : ℝ) 1) :
    ‖(∏ i, (x.1 i : ℂ)^α i) * (∏ j, (a j : ℂ)^δ j)‖ ≤
      ‖MvPolynomial.eval (elementaryGrowthVariables (elementaryCover
        (x + elementaryCubeLinear m n u) a b)) (windowPolynomial α δ)‖ := by
  have hquad (t : ℝ) : ‖(2 : ℂ) * (1 + (t : ℂ)^2)‖ = 2 * (1 + t^2) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [windowPolynomial, map_prod, norm_prod, Fintype.prod_sum_type]
  simp only [map_mul, map_ofNat, map_add, map_one, map_pow, MvPolynomial.eval_X, norm_pow,
    elementaryGrowthVariables, Sum.elim_inl, Sum.elim_inr, elementaryCover, ← Complex.ofReal_intCast,
    hquad, norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs]
  have hR :
      (∏ i : Fin m, |x.1 i| ^ α i) ≤
        ∏ i, (2 * (1 + (x.1 i + u (Fin.castAdd n i)) ^ 2)) ^ α i := by
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro i _
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_shifted_quadratic _ _ (hu (Fin.castAdd n i))) _
  have hZ :
      (∏ j : Fin r, |(a j : ℝ)| ^ δ j) ≤ ∏ j, (2 * (1 + (a j : ℝ) ^ 2)) ^ δ j := by
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro j _
    have hj := abs_le_shifted_quadratic (a j) 0 ⟨le_rfl, zero_le_one⟩
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [add_zero] using hj) _
  exact mul_le_mul hR hZ (Finset.prod_nonneg fun _ _ => by positivity)
    (Finset.prod_nonneg fun _ _ => by positivity)

private theorem weightedDerivative_le_lpNorm (α : Fin m → ℕ) (δ : Fin r → ℕ) (v : List X)
    (Q : DualOperators) (hQ : ∀ g : A,
      MvPolynomial.eval (elementaryGrowthVariables g) (windowPolynomial α δ) =
        (Q.map fun (d, ds) => d * elementaryDualWord ds g).sum)
    (f : E) (a : Fin r → ℤ) (b : F) (x : X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖(∏ i, (x.1 i : ℂ)^α i) * (∏ j, (a j : ℂ)^δ j)‖ *
        ‖listDerivative (fun u => f (elementaryCover u a b)) v x‖ ≤
      ((cubeMixedPartials (m + n)).map fun l =>
        ‖elementarySchwartz_weightedOperatorLp
          [(1, (l.map (fun j => elementaryCubeLinear m n (Pi.single j 1)) ++ v).map
            elementaryOneParameter)] Q p f‖).sum := by
  let T (u : Fin (m + n) → ℝ) := elementaryCover (x + elementaryCubeLinear m n u) a b
  have hT : Measurable T := elementaryCover_cube_measurable x a b
  let W := ‖(∏ i, (x.1 i : ℂ)^α i) * (∏ j, (a j : ℂ)^δ j)‖
  refine (mul_le_mul_of_nonneg_left (norm_listDerivative_le_integral_affineCube
    (elementaryCubeLinear m n) x (f.property.1 a b) v) (norm_nonneg _)).trans ?_
  rw [← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro l _
  let D := (l.map (fun j => elementaryCubeLinear m n (Pi.single j 1)) ++ v).map
    (elementaryOneParameter (r := r) (F := F))
  let g := elementarySchwartz_weightedOperator [(1, D)] Q f
  let g₀ := elementarySchwartz_weightedWord D [] f
  have hm := elementaryCover_map_cube_le x a b
  have hg : MemLp g p μ := elementarySchwartz_weightedOperator_memLp [(1, D)] Q p f
  have hg₀ : MemLp g₀ p μ := elementarySchwartz_weightedWord_memLp D [] (Fact.out : 1 ≤ p) f
  have hi {k : A → ℂ} (hk : MemLp k p μ) :
      Integrable (k ∘ T) (unitDerivativeCube (m + n)) :=
    memLp_one_iff_integrable.mp (((hk.mono_measure hm).comp_of_map hT.aemeasurable).mono_exponent Fact.out)
  have hb := integral_mono_ae ((hi hg₀).norm.const_mul W) (hi hg).norm (by
    filter_upwards [aes_unitDerivativeCube_mem (m + n)] with u hu
    change W * ‖g₀ (T u)‖ ≤ ‖g (T u)‖
    have hweight := monomial_le_windowPolynomial α δ x a b u hu
    rw [show g₀ (T u) = elementaryOrbitWord D f (T u) by
      simp [g₀, elementaryDualWord]]
    rw [show g (T u) = MvPolynomial.eval (elementaryGrowthVariables (T u))
          (windowPolynomial α δ) * elementaryOrbitWord D f (T u) by
        rw [elementarySchwartz_weightedOperator_apply, hQ]
        simp]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _))
  have hb' : W * (∫ u, ‖g₀ (T u)‖ ∂unitDerivativeCube (m + n)) ≤
      ∫ u, ‖g (T u)‖ ∂unitDerivativeCube (m + n) := by
    rw [← integral_const_mul]
    exact hb
  simp only [listDerivative_elementaryCover]
  rw [elementarySchwartz_weightedOperatorLp_norm]
  have hbound := hb'.trans (integral_norm_cube_le_lpNorm_of_map_le hT hm (Fact.out : 1 ≤ p) hg)
  simpa only [D, T, g₀, elementarySchwartz_weightedWord_apply, elementaryDualWord, List.map_nil,
    List.prod_nil, one_mul] using hbound


/-- Proposition D.1.10.6(2) in elementary coordinates. For each p ≥ 1,
the weighted invariant operator Lᵖ seminorms generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_weightedOperatorLp
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WithSeminorms (fun i : Operators × DualOperators =>
      (normSeminorm ℂ (Lp ℂ p μ)).comp
        (elementarySchwartz_weightedOperatorLp i.1 i.2 p).toLinearMap) := by
  classical
  let q (i : Operators × DualOperators) :=
    (normSeminorm ℂ (Lp ℂ p μ)).comp
      (elementarySchwartz_weightedOperatorLp i.1 i.2 p).toLinearMap
  refine elementarySchwartz_withSeminorms.congr
    (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
    (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
  · intro i
    have hq : Continuous (q i) := (elementarySchwartz_weightedOperatorLp i.1 i.2 p).continuous.norm
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous elementarySchwartz_withSeminorms (q i) hq
    exact ⟨s, C, fun f => hC f⟩
  · rintro ⟨α, β, γ, δ⟩
    obtain ⟨Q, hQ⟩ := elementaryPolynomial_exists_dualWords (n := n) (F := F) (windowPolynomial α δ)
    let L := elementaryDirectionList β γ
    let v : List X := List.ofFn (fun i : Fin L.length => elementaryFibreBasis m n (L.get i))
    have hpartial (f : E) (a : Fin r → ℤ) (b : F) (x : X) :
        listDerivative (fun u => f (elementaryCover u a b)) v x =
          elementaryPartial f β γ x a b := by
      rw [elementaryPartial_eq_basis]
      change iteratedFDeriv ℝ v.length (fun u => f (elementaryCover u a b)) x v.get =
        iteratedFDeriv ℝ L.length (fun u => f (elementaryCover u a b)) x
          (fun i => elementaryFibreBasis m n (L.get i))
      have len : v.length = L.length := List.length_ofFn
      have hget : v.get = fun i => elementaryFibreBasis m n (L.get (Fin.cast len i)) := by
        funext i
        exact List.get_ofFn _ i
      rw [hget]
      clear hget
      generalize v.length = k at len ⊢
      subst k
      rfl
    let C := cubeMixedPartials (m + n)
    let index (l : List (Fin (m + n))) : Operators × DualOperators :=
      ([(1, (l.map (fun j => elementaryCubeLinear m n (Pi.single j 1)) ++ v).map
        elementaryOneParameter)], Q)
    let s := (C.map index).toFinset
    refine ⟨s, (C.length : ℝ), fun f => ?_⟩
    have hSum :
        (C.map (fun l => q (index l) f)).sum ≤ (C.length : ℝ) * (s.sup q) f := by
      calc
        _ ≤ (C.map (fun _ => (s.sup q) f)).sum := by
          apply List.sum_le_sum
          intro l hl
          exact (Finset.le_sup (f := q) (List.mem_toFinset.mpr (List.mem_map_of_mem hl))) f
        _ = _ := by simp [nsmul_eq_mul]
    have hnonneg : 0 ≤ (C.length : ℝ) * (s.sup q) f := by positivity
    change (elementarySchwartzBound f.val (α, β, γ, δ)).toReal ≤
      (C.length : ℝ) * (s.sup q) f
    apply ENNReal.toReal_le_of_le_ofReal hnonneg
    unfold elementarySchwartzBound
    refine iSup_le fun x => iSup_le fun a => iSup_le fun b => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hb := weightedDerivative_le_lpNorm α δ v Q hQ f a b x p
    rw [hpartial] at hb
    simpa only [coe_nnnorm, norm_mul] using hb.trans hSum


end
end Masullo
