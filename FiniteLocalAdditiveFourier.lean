import AdelicCharacters
import FiniteLocalZeta
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.RingTheory.Valuation.Integral

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField Pointwise RestrictedProduct WithZero nonZeroDivisors

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev O := v.adicCompletionIntegers F

private def finitePlaceSingleBlock (x : K F v) :
    Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, (w.adicCompletionIntegers F).toSubring]_[𝓟 ({v}ᶜ)] :=
  ⟨Function.update (fun w : HeightOneSpectrum (𝓞 F) ↦ (0 : w.adicCompletion F)) v x,
    Filter.eventually_principal.mpr (fun w hw ↦ by
      rw [Function.update_of_ne (show w ≠ v from hw)]
      exact (w.adicCompletionIntegers F).zero_mem)⟩

private theorem finitePlaceSingleBlock_continuous : Continuous (finitePlaceSingleBlock F v) := by
  apply RestrictedProduct.isEmbedding_coe_of_principal.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro w
  by_cases hw : w = v
  · subst w
    change Continuous (fun x : K F v ↦ finitePlaceSingleBlock F v x v)
    have he : (fun x : K F v ↦ finitePlaceSingleBlock F v x v) = id := by
      funext x
      change Function.update (fun w : HeightOneSpectrum (𝓞 F) ↦ (0 : w.adicCompletion F)) v x v = x
      exact Function.update_self v x _
    rw [he]
    exact continuous_id
  · simpa [finitePlaceSingleBlock, Function.comp_def, Function.update_of_ne hw] using
      (continuous_const : Continuous (fun _ : K F v ↦ (0 : K F w)))

private def finitePlaceSingle (x : K F v) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (Filter.le_principal_iff.mpr (by simp))
    (finitePlaceSingleBlock F v x)

@[simp] private theorem finitePlaceSingle_self (x : K F v) : finitePlaceSingle F v x v = x := by
  change Function.update (fun w : HeightOneSpectrum (𝓞 F) ↦ (0 : w.adicCompletion F)) v x v = x
  exact Function.update_self v x _

private theorem finitePlaceSingle_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (x : K F v) :
    finitePlaceSingle F v x w = 0 := by
  change Function.update (fun w : HeightOneSpectrum (𝓞 F) ↦ (0 : w.adicCompletion F)) v x w = 0
  exact Function.update_of_ne hw x _

/-- The additive inclusion of the completion at a single finite place into
the adeles, with every other coordinate zero. -/
def finitePlaceAdditiveInsert : K F v →+ Adeles F where
  toFun x := finiteAdelicTranslation F (finitePlaceSingle F v x)
  map_zero' := by
    refine Prod.ext ?_ ?_
    · rfl
    apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst w
      exact finitePlaceSingle_self F v 0
    · exact finitePlaceSingle_of_ne F v hw 0
  map_add' x y := by
    apply Prod.ext (show (0 : InfiniteAdeleRing F) = 0 + 0 by simp)
    apply RestrictedProduct.ext
    intro w
    change finitePlaceSingle F v (x + y) w =
      finitePlaceSingle F v x w + finitePlaceSingle F v y w
    by_cases hw : w = v
    · subst w; simp
    · simp [finitePlaceSingle_of_ne F v hw]

theorem finitePlaceAdditiveInsert_continuous : Continuous (finitePlaceAdditiveInsert F v) :=
  continuous_const.prodMk ((RestrictedProduct.continuous_inclusion _).comp
    (finitePlaceSingleBlock_continuous F v))

/-- The additive character at a finite place induced by the global trace character. -/
def finitePlaceTraceCharacter : K F v →+ Additive Circle :=
  (standardAdelicCharacter F).comp (finitePlaceAdditiveInsert F v)

theorem finitePlaceTraceCharacter_continuous : Continuous (finitePlaceTraceCharacter F v) :=
  (standardAdelicCharacter_continuous F).comp (finitePlaceAdditiveInsert_continuous F v)

theorem finitePlaceTraceCharacter_kernel_open :
    IsOpen {x : K F v | finitePlaceTraceCharacter F v x = 0} :=
  (standardAdelicCharacter_finite_kernel_open F).preimage
    ((RestrictedProduct.continuous_inclusion _).comp (finitePlaceSingleBlock_continuous F v))

/-- Each finite component of the global additive character is nontrivial. -/
theorem finitePlaceTraceCharacter_nontrivial : ∃ x, finitePlaceTraceCharacter F v x ≠ 0 := by
  by_contra! h
  let a := finitePlaceAdditiveInsert F v 1
  have hall (x : F) : standardAdelicCharacter F (a * algebraMap F (Adeles F) x) = 0 := by
    have he : a * algebraMap F (Adeles F) x =
        finitePlaceAdditiveInsert F v (algebraMap F (K F v) x) := by
      apply Prod.ext
      · change (0 : InfiniteAdeleRing F) * _ = 0
        exact zero_mul _
      · apply RestrictedProduct.ext
        intro w
        change finitePlaceSingle F v 1 w * algebraMap F (K F w) x =
          finitePlaceSingle F v (algebraMap F (K F v) x) w
        by_cases hw : w = v
        · subst w; simp
        · simp [finitePlaceSingle_of_ne F v hw]
    rw [he]
    exact h _
  obtain ⟨x, hx⟩ := (standardAdelicCharacter_annihilator F a).mp hall
  have h₁ : algebraMap F (InfiniteAdeleRing F) x = 0 := congrArg Prod.fst hx
  have hx₀ : x = 0 := (algebraMap F (InfiniteAdeleRing F)).injective (by simpa using h₁)
  have h₂ : algebraMap F (K F v) x = 1 :=
    (congrArg (fun z : Adeles F ↦ z.2 v) hx).trans (finitePlaceSingle_self F v 1)
  simp [hx₀] at h₂

private theorem finitePlaceInteger_mem_iff_norm (x : K F v) :
    x ∈ (O F v : Set (K F v)) ↔ ‖x‖ ≤ 1 := by
  have hq : (1 : ℝ≥0) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  change x ∈ v.adicCompletionIntegers F ↔ _
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def]
  exact (WithZeroMulInt.toNNReal_le_one_iff hq).symm

/-- The annihilator of the integer ring for the finite component of the
standard global additive character. -/
def finitePlaceIntegerAnnihilator : Set (K F v) :=
  {y | ∀ x ∈ (O F v : Set (K F v)), finitePlaceTraceCharacter F v (x * y) = 0}

private abbrev FinA := FiniteAdeleRing (𝓞 F) F
private abbrev diagF := algebraMap F (FinA F)
private abbrev finitePhase (b : FinA F) := standardAdelicCharacter F (finiteAdelicTranslation F b)

private theorem finiteDiagonal_dense : DenseRange (diagF F) := by
  intro b
  apply mem_closure_iff_nhds.mpr
  intro U hU
  have hc : Continuous (fun z : FinA F ↦ b - z) := continuous_const.sub continuous_id
  have hpre : (fun z : FinA F ↦ b - z) ⁻¹' U ∈ 𝓝 0 :=
    hc.continuousAt.preimage_mem_nhds (by simpa only [sub_zero] using hU)
  obtain ⟨n, hn, hsub⟩ := finiteIntegralAdeles_nat_mul_subset_nhds F hpre
  obtain ⟨x, hx⟩ := finiteAdele_sub_diagonal F b
  obtain ⟨z, u, hu, he⟩ := finiteIntegralAdeles_mod_nat F _ hx n hn
  refine ⟨diagF F (x + (z : F)), ?_, ⟨_, rfl⟩⟩
  have hp := hsub ⟨u, hu, rfl⟩
  change b - (n : FinA F) * u ∈ U at hp
  have h' : b - (n : FinA F) * u = diagF F (x + (z : F)) := by
    rw [map_add]
    rw [sub_eq_iff_eq_add, add_assoc, ← he, add_sub_cancel]
  rwa [← h']

private theorem finitePlaceSingle_mul (b : FinA F) (y : K F v) :
    b * finitePlaceSingle F v y = finitePlaceSingle F v (b v * y) := by
  apply RestrictedProduct.ext
  intro w
  change b w * finitePlaceSingle F v y w = finitePlaceSingle F v (b v * y) w
  by_cases hw : w = v
  · subst w
    simp
  · simp [finitePlaceSingle_of_ne F v hw]

/- Adapted from RiemannMasullo/ForMathlib/RingTheory/Trace/Defs.lean,
   commit c5e66715f8d454ff5053246d6602bafb6890661f (Apache-2.0). -/
/-- If an algebra projection admits an additive section compatible with multiplication,
the trace of a lifted element projects to its trace in the quotient algebra.
The images of a finite basis of the original algebra span the quotient. -/
private theorem trace_of_algebra_projection
    {R A K B ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field K] [CommRing B] [Algebra K B] [Fintype ι]
    (b : Module.Basis ι R A) (p : R →+* K) (hp : Surjective p)
    (q : A →+* B) (s : B →+ A) (hqs : ∀ z, q (s z) = z)
    (hq : ∀ r, q (algebraMap R A r) = algebraMap K B (p r))
    (hs : ∀ a z, s (q a * z) = a * s z) :
    Module.Finite K B ∧ ∀ x, p (Algebra.trace R A (s x)) = Algebra.trace K B x := by
  classical
  let c (i : ι) : B →ₗ[K] K :=
    { toFun := fun z ↦ p (b.repr (s z) i)
      map_add' := fun z w ↦ by simp
      map_smul' := fun k z ↦ by
        obtain ⟨r, rfl⟩ := hp k
        change p (b.repr (s (p r • z)) i) = p r * p (b.repr (s z) i)
        rw [Algebra.smul_def]
        rw [← hq, hs, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul] }
  have hsum (z : B) : ∑ i, c i z • q (b i) = z := by
    have h := congrArg q (b.sum_repr (s z))
    change ∑ i, p (b.repr (s z) i) • q (b i) = z
    simpa only [hqs, map_sum, Algebra.smul_def, map_mul, hq] using h
  let f : A →ₛₗ[p] B :=
    { toFun := q
      map_add' := map_add q
      map_smul' := fun r z ↦ by simp only [Algebra.smul_def, map_mul, hq] }
  let : RingHomSurjective p := ⟨hp⟩
  let : Module.Finite R A := Module.Finite.of_basis b
  have hfinite : Module.Finite K B := Module.Finite.of_surjective f fun z ↦ ⟨s z, hqs z⟩
  refine ⟨hfinite, fun x ↦ ?_⟩
  have hm : Algebra.lmul K B x =
      ∑ i, (c i).smulRight (x * q (b i)) := by
    ext z
    change x * z = (∑ i, (c i).smulRight (x * q (b i))) z
    simp only [ LinearMap.sum_apply,
      LinearMap.smulRight_apply, ← mul_smul_comm, ← Finset.mul_sum, hsum]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, map_sum, Algebra.trace_apply]
  rw [hm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_smulRight, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  change p (b.repr (s x * b i) i) = p (b.repr (s (x * q (b i))) i)
  rw [mul_comm x, hs, mul_comm (s x)]

private abbrev ratPlace := v.under (𝓞 ℚ)

private def finitePlaceEval : Adeles F →+* K F v :=
  (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) ↦ K F w) v).comp
    (RingHom.snd _ _)

private theorem finitePlaceEval_insert (x : K F v) :
    finitePlaceEval F v (finitePlaceAdditiveInsert F v x) = x :=
  finitePlaceSingle_self F v x

private theorem finitePlaceInsert_mul (a : Adeles F) (x : K F v) :
    a * finitePlaceAdditiveInsert F v x = finitePlaceAdditiveInsert F v (finitePlaceEval F v a * x) :=
  Prod.ext (mul_zero _) (finitePlaceSingle_mul F v a.2 x)

/-- A trace of an adele supported at one place is the adele supported at
the place below it with coordinate the local field trace. -/
theorem relativeAdelicTraceRat_finitePlaceInsert :
    let u := ratPlace F v
    letI := (finiteCompletionMap ℚ F v).toAlgebra
    Module.Finite (u.adicCompletion ℚ) (K F v) ∧ ∀ x : K F v,
      relativeAdelicTraceRat F (finitePlaceAdditiveInsert F v x) =
        finitePlaceAdditiveInsert ℚ u (Algebra.trace (u.adicCompletion ℚ) (K F v) x) := by
  let u := ratPlace F v
  letI := (finiteCompletionMap ℚ F v).toAlgebra
  letI := (adelesExtension ℚ F).toAlgebra
  let p := finitePlaceEval ℚ u
  let q := finitePlaceEval F v
  let s := finitePlaceAdditiveInsert F v
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  have hq (r : Adeles ℚ) : q (algebraMap (Adeles ℚ) (Adeles F) r) =
      algebraMap (u.adicCompletion ℚ) (K F v) (p r) := rfl
  obtain ⟨hf, htr⟩ := trace_of_algebra_projection b p
    (fun z ↦ ⟨finitePlaceAdditiveInsert ℚ u z, finitePlaceEval_insert ℚ u z⟩)
    q s (finitePlaceEval_insert F v) hq (fun a x ↦ (finitePlaceInsert_mul F v a x).symm)
  refine ⟨hf, fun x ↦ ?_⟩
  let e := finitePlaceAdditiveInsert ℚ u 1
  let t := relativeAdelicTraceRat F (s x)
  have he : adelesExtension ℚ F e * s x = s x := by
    rw [finitePlaceInsert_mul]
    change s (q (algebraMap (Adeles ℚ) (Adeles F) e) * x) = s x
    rw [hq, show p e = 1 from finitePlaceEval_insert ℚ u 1, map_one, one_mul]
  have ht : e * t = t := by
    dsimp only [t]
    rw [← relativeAdelicTraceRat_mul_rat, he]
  have ht' := finitePlaceInsert_mul ℚ u t 1
  change t * e = finitePlaceAdditiveInsert ℚ u (p t * 1) at ht'
  rw [mul_comm t e, ht, mul_one] at ht'
  exact ht'.trans (congrArg (finitePlaceAdditiveInsert ℚ u) (htr x))

/-- The finite-place character is the rational character at the place below,
applied to the trace of the completed field extension. -/
theorem finitePlaceTraceCharacter_eq_localTrace (x : K F v) :
    let u := ratPlace F v
    letI := (finiteCompletionMap ℚ F v).toAlgebra
    finitePlaceTraceCharacter F v x = rationalAdelicCharacter
      (finitePlaceAdditiveInsert ℚ u (Algebra.trace (u.adicCompletion ℚ) (K F v) x)) := by
  exact congrArg rationalAdelicCharacter ((relativeAdelicTraceRat_finitePlaceInsert F v).2 x)

/-- The local character has kernel given by the elements with integral
completed trace. -/
theorem finitePlaceTraceCharacter_eq_zero_iff_trace_integral (x : K F v) :
    let u := ratPlace F v
    letI := (finiteCompletionMap ℚ F v).toAlgebra
    finitePlaceTraceCharacter F v x = 0 ↔
      Algebra.trace (u.adicCompletion ℚ) (K F v) x ∈ u.adicCompletionIntegers ℚ := by
  let u := ratPlace F v
  letI := (finiteCompletionMap ℚ F v).toAlgebra
  rw [finitePlaceTraceCharacter_eq_localTrace]
  let z := Algebra.trace (u.adicCompletion ℚ) (K F v) x
  change rationalAdelicCharacter (finiteAdelicTranslation ℚ (finitePlaceSingle ℚ u z)) = 0 ↔ _
  rw [rationalAdelicCharacter_finite_eq_zero_iff, mem_finiteIntegralAdeles_iff]
  constructor
  · intro h
    simpa only [finitePlaceSingle_self] using h u
  · intro h w
    by_cases hw : w = u
    · subst w
      rwa [finitePlaceSingle_self]
    · rw [finitePlaceSingle_of_ne ℚ u hw]
      exact zero_mem _

private theorem globalCodifferent_mem_iff (z : F) :
    z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) ↔
      ∀ x : 𝓞 F, finitePhase F (diagF F ((x : F) * z)) = 0 := by
  rw [Submodule.mem_traceDual]
  simp only [Submodule.one_eq_range, LinearMap.mem_range, RingHom.mem_range]
  constructor
  · intro h x
    apply (standardAdelicCharacter_finite_diagonal_eq_zero_iff F _).mpr
    simpa [Algebra.traceForm_apply, mul_comm] using h (x : F) ⟨x, rfl⟩
  · rintro h x ⟨a, rfl⟩
    simpa [Algebra.traceForm_apply, mul_comm] using
      (standardAdelicCharacter_finite_diagonal_eq_zero_iff F _).mp (h a)

private theorem finitePhase_codifferent_mul_integral
    {z : F} (hz : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F))
    {b : FinA F} (hb : b ∈ finiteIntegralAdeles F) :
    finitePhase F (b * diagF F z) = 0 := by
  have hU : {a : FinA F | finitePhase F (a * diagF F z) = 0} ∈ 𝓝 (0 : FinA F) :=
    ((standardAdelicCharacter_finite_kernel_open F).preimage
      (continuous_id.mul continuous_const)).mem_nhds (by
        change finitePhase F (0 * diagF F z) = 0
        rw [zero_mul]
        exact (standardAdelicCharacter F).map_zero)
  obtain ⟨n, hn, hsub⟩ := finiteIntegralAdeles_nat_mul_subset_nhds F hU
  obtain ⟨x, u, hu, he⟩ := finiteIntegralAdeles_mod_nat F b hb n hn
  have h := hsub ⟨u, hu, rfl⟩
  change finitePhase F (((n : FinA F) * u) * diagF F z) = 0 at h
  change standardAdelicCharacter F (finiteAdelicTranslation F (b * diagF F z)) = 0
  rw [he, add_mul]
  have hadd (a c : FinA F) :
      finiteAdelicTranslation F (a + c) = finiteAdelicTranslation F a +
        finiteAdelicTranslation F c := Prod.ext (zero_add _).symm rfl
  rw [hadd, map_add, ← map_mul]
  change finitePhase F (diagF F ((x : F) * z)) +
    finitePhase F (((n : FinA F) * u) * diagF F z) = 0
  rw [(globalCodifferent_mem_iff F z).mp hz x, h, add_zero]

/-- The standard character is trivial on all integral finite adeles. -/
theorem standardAdelicCharacter_finite_integral {b : FinA F}
    (hb : b ∈ finiteIntegralAdeles F) : finitePhase F b = 0 := by
  have h₁ : (1 : F) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) :=
    Submodule.one_le_traceDual_one (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  simpa only [map_one, mul_one] using finitePhase_codifferent_mul_integral F h₁ hb

@[simp] theorem finitePlaceAdditiveInsert_finite_apply_self (x : K F v) :
    (finitePlaceAdditiveInsert F v x).2 v = x :=
  finitePlaceSingle_self F v x

theorem finitePlaceAdditiveInsert_finite_apply_ne {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) (x : K F v) : (finitePlaceAdditiveInsert F v x).2 w = 0 :=
  finitePlaceSingle_of_ne F v hw x

theorem finitePlaceAdditiveInsert_finite_mul (b : FinA F) (x : K F v) :
    b * (finitePlaceAdditiveInsert F v x).2 = (finitePlaceAdditiveInsert F v (b v * x)).2 :=
  finitePlaceSingle_mul F v b x

private theorem finitePlaceSingle_mem_integral {x : K F v}
    (hx : x ∈ (O F v : Set (K F v))) : finitePlaceSingle F v x ∈ finiteIntegralAdeles F := by
  apply (mem_finiteIntegralAdeles_iff F _).mpr
  intro w
  by_cases hw : w = v
  · subst w
    change finitePlaceSingle F v x v ∈ (O F v : Set (K F v))
    simpa only [finitePlaceSingle_self] using hx
  · rw [finitePlaceSingle_of_ne F v hw]
    exact zero_mem _

private theorem finitePhase_of_local_zero (b : FinA F)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), finitePlaceTraceCharacter F w (b w) = 0) :
    finitePhase F b = 0 := by
  let T := (eventually_cofinite.mp b.property).toFinset
  have hT (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) :
      b w ∈ w.adicCompletionIntegers F := by
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).mpr h)
  let d : FinA F := ∑ w ∈ T, finitePlaceSingle F w (b w)
  have hd (w : HeightOneSpectrum (𝓞 F)) : d w = if w ∈ T then b w else 0 := by
    let p : FinA F →+* K F w :=
      RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) ↦ K F w) w
    change p (∑ t ∈ T, finitePlaceSingle F t (b t)) = _
    rw [map_sum]
    by_cases hw : w ∈ T
    · rw [ite_eq_left hw, Finset.sum_eq_single_of_mem w hw]
      · exact finitePlaceSingle_self F w (b w)
      · intro t _ ht
        exact finitePlaceSingle_of_ne F t (Ne.symm ht) (b t)
    · rw [ite_eq_right hw, Finset.sum_eq_zero]
      intro t ht
      have hwt : w ≠ t := fun e ↦ hw (by rwa [e])
      exact finitePlaceSingle_of_ne F t hwt (b t)
  have hr : b - d ∈ finiteIntegralAdeles F := by
    apply (mem_finiteIntegralAdeles_iff F _).mpr
    intro w
    change b w - d w ∈ w.adicCompletionIntegers F
    rw [hd]
    by_cases hw : w ∈ T
    · rw [ite_eq_left hw, sub_self]
      exact zero_mem _
    · simpa only [ite_eq_right hw, sub_zero] using hT w hw
  let χ : FinA F →+ Additive Circle :=
    (standardAdelicCharacter F).comp (AddMonoidHom.inr _ _)
  have hχ : χ d = 0 := by
    change χ (∑ w ∈ T, finitePlaceSingle F w (b w)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun w _ ↦ hb w)
  change χ b = 0
  have he : χ (b - d) = 0 := standardAdelicCharacter_finite_integral F hr
  rwa [map_sub, hχ, sub_zero] at he

/-- The annihilator of the integral finite adeles is the product of the
local annihilators, inside the finite adele ring. -/
theorem finiteIntegralAdeles_annihilator_iff (y : FinA F) :
    (∀ x ∈ finiteIntegralAdeles F, finitePhase F (x * y) = 0) ↔
      ∀ w : HeightOneSpectrum (𝓞 F), y w ∈ finitePlaceIntegerAnnihilator F w := by
  constructor
  · intro h w x hx
    have hp := h (finitePlaceSingle F w x) (finitePlaceSingle_mem_integral F w hx)
    rw [mul_comm, finitePlaceSingle_mul F w, mul_comm] at hp
    exact hp
  · intro h x hx
    apply finitePhase_of_local_zero F
    intro w
    exact h w (x w) ((mem_finiteIntegralAdeles_iff F x).mp hx w)

private theorem finitePlaceIntegerAnnihilator_contains_codifferent :
    (algebraMap F (K F v)) '' (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F) ⊆
      finitePlaceIntegerAnnihilator F v := by
  rintro _ ⟨z, hz, rfl⟩ x hx
  have h := finitePhase_codifferent_mul_integral F hz (finitePlaceSingle_mem_integral F v hx)
  rw [mul_comm, finitePlaceSingle_mul F v, mul_comm] at h
  exact h

private theorem finitePlaceIntegerAnnihilator_closed :
    IsClosed (finitePlaceIntegerAnnihilator F v) := by
  change IsClosed {y | ∀ x ∈ (O F v : Set (K F v)), finitePlaceTraceCharacter F v (x * y) = 0}
  simp only [← Set.iInter_ofPred]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
    isClosed_eq ((finitePlaceTraceCharacter_continuous F v).comp
      (continuous_const.mul continuous_id)) continuous_const

/-- The finite-place annihilator is the closure of the global trace-dual
lattice in the completion at that place. -/
theorem finitePlaceIntegerAnnihilator_eq_completedCodifferent :
    finitePlaceIntegerAnnihilator F v = closure ((algebraMap F (K F v)) ''
      (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F)) := by
  apply Subset.antisymm _ (closure_minimal
    (finitePlaceIntegerAnnihilator_contains_codifferent F v) (finitePlaceIntegerAnnihilator_closed F v))
  intro y hy
  let a := finitePlaceSingle F v y
  let I : Set (FinA F) := finiteIntegralAdeles F
  let W : Set (FinA F × FinA F) := {z | finitePhase F (z.1 * z.2) = 0}
  have hW : IsOpen W :=
    (standardAdelicCharacter_finite_kernel_open F).preimage (continuous_fst.mul continuous_snd)
  have hIW : I ×ˢ {a} ⊆ W := by
    rintro ⟨b, c⟩ ⟨hb, hc⟩
    change c = a at hc
    subst c
    change finitePhase F (b * finitePlaceSingle F v y) = 0
    rw [finitePlaceSingle_mul F v]
    exact hy (b v) ((mem_finiteIntegralAdeles_iff F b).mp hb v)
  obtain ⟨U, V, _, hVo, hIU, haV, hUV⟩ :=
    generalized_tube_lemma (isCompact_finiteIntegralAdeles F) isCompact_singleton hW hIW
  have hV : V ∈ 𝓝 a := hVo.mem_nhds (haV (mem_singleton a))
  apply mem_closure_iff_nhds.mpr
  intro T hT
  let ev (b : FinA F) := b v
  have hev : Continuous ev := RestrictedProduct.continuous_eval v
  have hpre : ev ⁻¹' T ∈ 𝓝 a := hev.continuousAt.preimage_mem_nhds (by
    change T ∈ 𝓝 (finitePlaceSingle F v y v)
    rwa [finitePlaceSingle_self])
  obtain ⟨_, ⟨hbV, hbT⟩, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (finiteDiagonal_dense F a) _ (inter_mem hV hpre)
  refine ⟨algebraMap F (K F v) z, hbT, z, (globalCodifferent_mem_iff F z).mpr ?_, rfl⟩
  intro x
  have hx : diagF F (x : F) ∈ I := (finiteDiagonal_mem_integral F _).mpr ⟨x, rfl⟩
  have ht := hUV (show (diagF F (x : F), diagF F z) ∈ U ×ˢ V from ⟨hIU hx, hbV⟩)
  change finitePhase F (diagF F (x : F) * diagF F z) = 0 at ht
  rwa [← map_mul] at ht

private theorem finitePlaceIntegerAnnihilator_lower {x y : K F v} (hx : x ∈ finitePlaceIntegerAnnihilator F v)
    (hy : ‖y‖ ≤ ‖x‖) : y ∈ finitePlaceIntegerAnnihilator F v := by
  by_cases hx₀ : x = 0
  · have he : y = 0 := by
      apply norm_eq_zero.mp
      simpa [hx₀] using hy
    simp [he, finitePlaceIntegerAnnihilator]
  have hdiv : y / x ∈ O F v := (finitePlaceInteger_mem_iff_norm F v _).2 (by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hx₀)).2 hy)
  intro u hu
  have hh := hx (u * (y / x)) ((O F v).mul_mem _ _ hu hdiv)
  rwa [mul_assoc, div_mul_cancel₀ y hx₀] at hh

theorem finitePlaceUniformizer_norm_zpow (n : ℤ) :
    ‖((chosenFiniteUniformizer F v ^ n : (K F v)ˣ) : K F v)‖ =
      (v.asIdeal.absNorm : ℝ) ^ (-n) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_zpow, zpow_neg]

/-- The finite character has an intrinsic conductor: the annihilator of the
integer ring is one closed valuation ball. -/
theorem finitePlaceIntegerAnnihilator_eq_ball :
    ∃ n : ℤ, finitePlaceIntegerAnnihilator F v =
      {y : K F v | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)} := by
  let q := (v.asIdeal.absNorm : ℝ)
  let π := chosenFiniteUniformizer F v
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < q := zero_lt_one.trans hq
  let B := finitePlaceIntegerAnnihilator F v
  let P (n : ℤ) := ((π ^ n : (K F v)ˣ) : K F v) ∈ B
  have hnorm (n : ℤ) : ‖((π ^ n : (K F v)ˣ) : K F v)‖ = q ^ (-n) :=
    finitePlaceUniformizer_norm_zpow F v n
  have hm : Monotone P := by
    intro i j hij hi
    exact finitePlaceIntegerAnnihilator_lower F v hi (by
      rw [hnorm, hnorm]
      exact zpow_le_zpow_right₀ hq.le (neg_le_neg hij))
  have hhex (y : K F v) (hy : y ≠ 0) : ∃ n : ℤ, ‖y‖ = q ^ (-n) :=
    iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) (Units.mk0 y hy)
  obtain ⟨x, hx⟩ := finitePlaceTraceCharacter_nontrivial F v
  have hx₀ : x ≠ 0 := fun h ↦ hx (h ▸ map_zero _)
  have hxB : x ∉ B := fun h ↦ hx (by simpa only [one_mul] using h 1 (O F v).one_mem)
  obtain ⟨i, hi⟩ := hhex x hx₀
  have hiP : ¬ P i := fun h ↦ hxB (finitePlaceIntegerAnnihilator_lower F v h ((hi.trans (hnorm i).symm).le))
  have hbd : ∃ i : ℤ, ∀ j : ℤ, P j → i ≤ j :=
    ⟨i, fun j hj ↦ le_of_not_ge fun hji ↦ hiP (hm hji hj)⟩
  have hnh := (finitePlaceTraceCharacter_kernel_open F v).mem_nhds
    (show finitePlaceTraceCharacter F v 0 = 0 from map_zero _)
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp hnh
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  have hkP : P k := by
    intro u hu
    apply hsmall
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hnorm]
    calc
      _ ≤ 1 * q ^ (-(k : ℤ)) :=
        mul_le_mul_of_nonneg_right ((finitePlaceInteger_mem_iff_norm F v u).1 hu) (by positivity)
      _ < ε := by simpa only [one_mul, zpow_neg, zpow_natCast, inv_pow] using hk
  obtain ⟨n, hn, hmin⟩ := Int.exists_least_of_bdd hbd ⟨k, hkP⟩
  refine ⟨n, ?_⟩
  ext y
  constructor
  · intro hy
    by_cases hy₀ : y = 0
    · simpa only [Set.mem_ofPred_eq, hy₀, norm_zero] using zpow_nonneg hq₀.le (-n)
    obtain ⟨m, hm'⟩ := hhex y hy₀
    have hPm : P m := finitePlaceIntegerAnnihilator_lower F v hy (by rw [hnorm, hm'])
    exact hm'.le.trans (zpow_le_zpow_right₀ hq.le (neg_le_neg (hmin m hPm)))
  · intro hy
    exact finitePlaceIntegerAnnihilator_lower F v hn (by exact hy.trans_eq (hnorm n).symm)

private theorem val_completion_integer (a : 𝓞 F) :
    Valued.v (algebraMap F (K F v) (a : F)) = v.intValuation a :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (a : F)).trans
    (v.valuation_of_algebraMap a)

private theorem norm_completion_integer_le_iff (a : 𝓞 F) (d : ℕ) :
    ‖algebraMap F (K F v) (a : F)‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(d : ℤ)) ↔
      a ∈ v.asIdeal ^ d := by
  have hq : (1 : ℝ≥0) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : (v.asIdeal.absNorm : ℝ≥0) ≠ 0 := (zero_lt_one.trans hq).ne'
  rw [FinitePlace.norm_def, val_completion_integer, ← v.intValuation_le_pow_iff_mem a d]
  have he : WithZeroMulInt.toNNReal hq₀ (WithZero.exp (-(d : ℤ))) =
      (v.asIdeal.absNorm : ℝ≥0) ^ (-(d : ℤ)) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    rfl
  rw [← NNReal.coe_natCast, ← NNReal.coe_zpow, ← he, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le

private theorem norm_completion_integer_lt_one_iff (a : 𝓞 F) :
    ‖algebraMap F (K F v) (a : F)‖ < 1 ↔ a ∈ v.asIdeal := by
  have hq : (1 : ℝ≥0) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [FinitePlace.norm_def, val_completion_integer, ← v.intValuation_lt_one_iff_mem a]
  exact WithZeroMulInt.toNNReal_lt_one_iff hq

/-- The radius of the annihilator ball is the residue cardinality to the
multiplicity of the place in the global different. -/
theorem finitePlaceIntegerAnnihilator_eq_differentBall :
    finitePlaceIntegerAnnihilator F v =
      {y : K F v | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))} := by
  let J := differentIdeal ℤ (𝓞 F)
  let d := multiplicity v.asIdeal J
  let q := (v.asIdeal.absNorm : ℝ)
  let D := algebraMap F (K F v)
  let Jf : FractionalIdeal (𝓞 F)⁰ F := J
  let C := Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  have hJf : Jf ≠ 0 := by simpa [Jf] using hJ
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have hC : (↑Jf⁻¹ : Submodule (𝓞 F) F) = C := by
    rw [show Jf = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F))⁻¹
      from coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv, FractionalIdeal.coe_dual_one]
  have hprod : Jf * Jf⁻¹ = 1 := mul_inv_cancel₀ hJf
  have hnormJ (a : 𝓞 F) (ha : a ∈ J) : ‖D (a : F)‖ ≤ (q ^ d)⁻¹ := by
    have hdvd : v.asIdeal ^ d ∣ J := pow_multiplicity_dvd _ _
    simpa only [zpow_neg, zpow_natCast] using
      (norm_completion_integer_le_iff F v a d).mpr ((Ideal.dvd_iff_le.mp hdvd) ha)
  have hfinite := FiniteMultiplicity.of_prime_left v.prime hJ
  have hnot : ¬ J ≤ v.asIdeal ^ (d + 1) :=
    fun h ↦ hfinite.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self d) (Ideal.dvd_iff_le.mpr h)
  obtain ⟨a, ha, hap⟩ := SetLike.not_le_iff_exists.mp hnot
  have ha₀ : a ≠ 0 := fun h ↦ hap (h ▸ zero_mem _)
  have hnorma : ‖D (a : F)‖ = (q ^ d)⁻¹ := by
    have hf := FiniteMultiplicity.of_prime_left v.prime
      (show Ideal.span ({a} : Set (𝓞 F)) ≠ 0 from Submodule.span_singleton_eq_bot.mp.mt ha₀)
    have hm : multiplicity v.asIdeal (Ideal.span {a}) = d := by
      apply le_antisymm
      · apply Nat.lt_succ_iff.mp
        by_contra! hh
        exact hap (Ideal.dvd_span_singleton.mp (pow_dvd_of_le_multiplicity hh))
      · exact hf.le_multiplicity_of_le_emultiplicity (pow_dvd_iff_le_emultiplicity.mp
          (Ideal.dvd_span_singleton.mpr ((Ideal.dvd_iff_le.mp (pow_multiplicity_dvd _ _)) ha)))
    change ‖algebraMap F (K F v) (a : F)‖ = _
    rw [FinitePlace.norm_def, val_completion_integer, v.intValuation_eq_exp_neg_multiplicity ha₀, hm,
      WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    change (↑((v.asIdeal.absNorm : ℝ≥0) ^ (-(d : ℤ))) : ℝ) = (q ^ d)⁻¹
    rw [NNReal.coe_zpow, zpow_neg, zpow_natCast]
    rfl
  have hmem {z : F} : z ∈ Jf⁻¹ ↔ z ∈ C := by
    change z ∈ (↑Jf⁻¹ : Submodule (𝓞 F) F) ↔ z ∈ C
    rw [hC]
  have hupper : finitePlaceIntegerAnnihilator F v ⊆ {y | ‖y‖ ≤ q ^ d} := by
    rw [finitePlaceIntegerAnnihilator_eq_completedCodifferent]
    apply closure_minimal _ (isClosed_le continuous_norm continuous_const)
    rintro _ ⟨z, hz, rfl⟩
    have hp : (a : F) * z ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := hprod ▸
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ ha) (hmem.mpr hz)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hp
    have he : ‖D (a : F)‖ * ‖D z‖ ≤ 1 := by
      rw [← norm_mul, ← map_mul, ← hb]
      simpa using (norm_completion_integer_le_iff F v b 0).mpr (by simp)
    rw [hnorma, inv_mul_le_iff₀ (pow_pos hq d), mul_one] at he
    exact he
  obtain ⟨n, hn⟩ := finitePlaceIntegerAnnihilator_eq_ball F v
  suffices hrad : q ^ d ≤ q ^ (-n) by
    exact Subset.antisymm hupper (fun y hy ↦ hn.symm ▸ (hy.trans hrad : ‖y‖ ≤ q ^ (-n)))
  by_contra! hrad
  have hle : Jf * Jf⁻¹ ≤ (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) := by
    apply FractionalIdeal.mul_le.mpr
    intro a' ha' z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha'
    have hp := hprod ▸ FractionalIdeal.mul_mem_mul ha' hz
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).mp hp
    have hzann := finitePlaceIntegerAnnihilator_contains_codifferent F v
      ⟨z, hmem.mp hz, rfl⟩
    have hznorm : ‖D z‖ ≤ q ^ (-n) := by rw [hn] at hzann; exact hzann
    have hcnorm : ‖D (c : F)‖ < 1 := by
      change ‖D (algebraMap (𝓞 F) F c)‖ < 1
      rw [hc, map_mul, norm_mul]
      calc
        _ ≤ (q ^ d)⁻¹ * q ^ (-n) := mul_le_mul (hnormJ b hb) hznorm (norm_nonneg _)
          (inv_nonneg.mpr (pow_nonneg hq.le _))
        _ < 1 := by rwa [inv_mul_lt_iff₀ (pow_pos hq d), mul_one]
    exact (FractionalIdeal.mem_coeIdeal _).mpr
      ⟨c, (norm_completion_integer_lt_one_iff F v c).mp hcnorm, hc⟩
  rw [hprod] at hle
  obtain ⟨b, hb, h1⟩ := (FractionalIdeal.mem_coeIdeal _).mp
    (hle (FractionalIdeal.mem_one_iff _ |>.mpr ⟨1, map_one _⟩) : (1 : F) ∈
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F))
  have hb₁ : b = 1 := (IsFractionRing.injective (𝓞 F) F)
    (h1.trans (map_one (algebraMap (𝓞 F) F)).symm)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hb₁ ▸ hb))

/-- At a prime away from the different, the integer ring is its own
annihilator. -/
theorem finitePlaceIntegerAnnihilator_eq_integerRing_of_not_dvd
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    finitePlaceIntegerAnnihilator F v = (O F v : Set (K F v)) := by
  rw [finitePlaceIntegerAnnihilator_eq_differentBall, multiplicity_eq_zero.mpr hv, pow_zero]
  ext y
  exact (finitePlaceInteger_mem_iff_norm F v y).symm

/-- At a prime dividing the different, the annihilator contains a
nonintegral frequency. -/
theorem finitePlaceIntegerAnnihilator_exists_nonintegral
    (hv : v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    ∃ y ∈ finitePlaceIntegerAnnihilator F v, y ∉ (O F v : Set (K F v)) := by
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  have hd : 0 < d := multiplicity_pos_of_dvd hv
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let y := ((chosenFiniteUniformizer F v ^ (-(d : ℤ)) : (K F v)ˣ) : K F v)
  have hy : ‖y‖ = (v.asIdeal.absNorm : ℝ) ^ d := by
    rw [finitePlaceUniformizer_norm_zpow F v (-(d : ℤ)), neg_neg, zpow_natCast]
  refine ⟨y, ?_, ?_⟩
  · rw [finitePlaceIntegerAnnihilator_eq_differentBall]
    exact hy.le
  · rw [finitePlaceInteger_mem_iff_norm, hy]
    exact not_le.mpr (one_lt_pow₀ hq hd.ne')

/-- The integral trace pairing over the completed rational field has the same
codifferent ball as the global trace-dual lattice. -/
theorem finitePlace_localTraceDual_eq_differentBall (y : K F v) :
    let u := ratPlace F v
    letI := (finiteCompletionMap ℚ F v).toAlgebra
    (∀ x ∈ (O F v : Set (K F v)),
      Algebra.trace (u.adicCompletion ℚ) (K F v) (x * y) ∈ u.adicCompletionIntegers ℚ) ↔
    ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) := by
  simp_rw [← finitePlaceTraceCharacter_eq_zero_iff_trace_integral F v]
  change y ∈ finitePlaceIntegerAnnihilator F v ↔ _
  rw [finitePlaceIntegerAnnihilator_eq_differentBall]
  rfl

private def finiteCompletionIntegerMap : O ℚ (ratPlace F v) →+* O F v where
  toFun x := ⟨finiteCompletionMap ℚ F v x.val, finiteCompletionMap_integral ℚ F v x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The completed integer ring is a finite module over the completed rational
integer ring. Compactness bounds the coordinates of the local integers in a
field basis. Multiplication by a sufficiently small scalar makes each
coordinate integral. -/
theorem finitePlace_integerRing_moduleFinite :
    letI := (finiteCompletionIntegerMap F v).toAlgebra
    Module.Finite (O ℚ (ratPlace F v)) (O F v) := by
  let u := ratPlace F v
  let A := O ℚ u
  let B := O F v
  let L := K ℚ u
  let E := K F v
  let j := finiteCompletionMap ℚ F v
  have hq : 1 < (u.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm u
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with
      non_trivial := ⟨((chosenFiniteUniformizer ℚ u).val)⁻¹, by
        rw [norm_inv, norm_finiteUniformizer ℚ u _ (chosenFiniteUniformizer_spec ℚ u), inv_inv]
        exact hq⟩ }
  letI : Algebra L E := j.toAlgebra
  letI : Algebra A B := (finiteCompletionIntegerMap F v).toAlgebra
  letI : ContinuousSMul L E := ⟨show Continuous (fun z : L × E ↦ j z.1 * z.2) from
    ((finiteCompletionMap_continuous ℚ F v).comp continuous_fst).mul continuous_snd⟩
  letI : Module.Finite L E := (relativeAdelicTraceRat_finitePlaceInsert F v).1
  let b := Module.Basis.ofVectorSpace L E
  have hscale (i : Module.Basis.ofVectorSpaceIndex L E) : ∃ c : L, c ≠ 0 ∧
      ∀ x ∈ (B : Set E), c * b.coord i x ∈ (A : Set L) := by
    have hc : Continuous (b.coord i) := by
      exact LinearMap.continuous_of_finiteDimensional (𝕜 := L) (E := E) (F' := L) (b.coord i)
    have hcompact : IsCompact ((b.coord i) '' (B : Set E)) := (finitePlaceIntegral_compact F v).image hc
    obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : L)).mp hcompact.isBounded
    have hM₀ : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hM₀) (inv_lt_one_of_one_lt₀ hq)
    let π := chosenFiniteUniformizer ℚ u
    refine ⟨π.val ^ n, pow_ne_zero _ π.ne_zero, fun x hx ↦ ?_⟩
    apply (finitePlaceInteger_mem_iff_norm ℚ u _).mpr
    have hb : ‖b.coord i x‖ ≤ M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hM ⟨x, hx, rfl⟩
    rw [norm_mul, norm_pow, norm_finiteUniformizer ℚ u _ (chosenFiniteUniformizer_spec ℚ u)]
    calc
      _ ≤ (max M 1)⁻¹ * max M 1 := mul_le_mul hn.le (hb.trans (le_max_left _ _))
        (norm_nonneg _) (inv_nonneg.mpr hM₀.le)
      _ = 1 := inv_mul_cancel₀ hM₀.ne'
  choose c hc hci using hscale
  let f (i : Module.Basis.ofVectorSpaceIndex L E) : B →ₗ[A] A :=
    { toFun := fun x ↦ ⟨c i * b.coord i x.val, hci i x.val x.property⟩
      map_add' x y := Subtype.ext (by
        change c i * b.coord i (x.val + y.val) = _
        rw [map_add, mul_add]
        rfl)
      map_smul' a x := Subtype.ext (by
        change c i * b.coord i (j a.val * x.val) = a.val * (c i * b.coord i x.val)
        rw [← show a.val • x.val = j a.val * x.val from rfl, map_smul, smul_eq_mul]
        ac_rfl) }
  apply Module.Finite.of_injective (LinearMap.pi f)
  intro x y hxy
  apply Subtype.ext
  apply b.equivFun.injective
  funext i
  change b.coord i x.val = b.coord i y.val
  apply mul_left_cancel₀ (hc i)
  exact congrArg Subtype.val (congrFun hxy i)

private theorem finiteCompletionIntegerMap_torsionFree :
    letI := (finiteCompletionIntegerMap F v).toAlgebra
    Module.IsTorsionFree (O ℚ (ratPlace F v)) (O F v) := by
  letI := (finiteCompletionIntegerMap F v).toAlgebra
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr
    (fun _ _ h ↦ Subtype.ext ((finiteCompletionMap ℚ F v).injective (congrArg Subtype.val h)))

/-- The different ideal for the actual extension of completed integer rings. -/
def finitePlaceCompletedDifferent : Ideal (O F v) :=
  letI := (finiteCompletionIntegerMap F v).toAlgebra
  letI := finiteCompletionIntegerMap_torsionFree F v
  differentIdeal (O ℚ (ratPlace F v)) (O F v)

private def finitePlaceIntegerUniformizer : O F v :=
  ⟨(chosenFiniteUniformizer F v).val, (finitePlaceInteger_mem_iff_norm F v _).mpr (by
    rw [norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)]
    have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact (inv_lt_one_of_one_lt₀ hq).le)⟩

/-- The completed different is generated by a uniformizer to the exponent
of the associated prime in the global different. -/
theorem finitePlaceCompletedDifferent_eq_span :
    finitePlaceCompletedDifferent F v =
      Ideal.span {finitePlaceIntegerUniformizer F v ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))} := by
  let u := ratPlace F v
  let A := O ℚ u
  let B := O F v
  let L := K ℚ u
  let E := K F v
  let j := finiteCompletionMap ℚ F v
  letI : Algebra L E := j.toAlgebra
  letI : Algebra A B := (finiteCompletionIntegerMap F v).toAlgebra
  letI : Algebra A E := (j.comp A.toSubring.subtype).toAlgebra
  letI : IsScalarTower A L E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite L E := (relativeAdelicTraceRat_finitePlaceInsert F v).1
  letI : Module.Finite A B := finitePlace_integerRing_moduleFinite F v
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  letI : Module.IsTorsionFree A B := finiteCompletionIntegerMap_torsionFree F v
  have hB := Valuation.valuationSubring.integers
    (Valued.v : Valuation E (WithZero (Multiplicative ℤ)))
  letI : IsIntegralClosure B A E := by
    refine ⟨Subtype.val_injective, fun {x} ↦ ⟨?_, ?_⟩⟩
    · intro hx
      exact hB.exists_of_le_one (hB.isIntegral_iff_v_le_one.mp (hx.tower_top (A := B)))
    · rintro ⟨b, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := A) b).algebraMap
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let a := finitePlaceIntegerUniformizer F v ^ d
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have ha : ‖(a.val : E)‖ = (q ^ d)⁻¹ := by
    change ‖(chosenFiniteUniformizer F v).val ^ d‖ = _
    rw [norm_pow, norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_pow]
  have ha₀ : a.val ≠ 0 := pow_ne_zero _ (chosenFiniteUniformizer F v).ne_zero
  have hdual : FractionalIdeal.dual A L (1 : FractionalIdeal B⁰ E) =
      FractionalIdeal.spanSingleton B⁰ (a.val : E)⁻¹ := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (↑(FractionalIdeal.dual A L (1 : FractionalIdeal B⁰ E)) : Submodule B E) =
      (↑(FractionalIdeal.spanSingleton B⁰ (a.val : E)⁻¹) : Submodule B E)
    rw [FractionalIdeal.coe_dual_one, FractionalIdeal.coe_spanSingleton]
    ext x
    rw [Submodule.mem_traceDual, Submodule.mem_span_singleton]
    simp only [Submodule.one_eq_range, LinearMap.mem_range, RingHom.mem_range,
      Algebra.traceForm_apply]
    have htrace : (∀ y : E, (∃ b : B, b.val = y) →
        ∃ c : A, c.val = Algebra.trace L E (x * y)) ↔ ‖x‖ ≤ q ^ d := by
      have hball : (∀ y ∈ (B : Set E), Algebra.trace L E (y * x) ∈ (A : Set L)) ↔
          ‖x‖ ≤ q ^ d := finitePlace_localTraceDual_eq_differentBall F v x
      rw [← hball]
      simp only [mul_comm x, SetLike.mem_coe, Subtype.exists, exists_prop, exists_eq_right]
    change (∀ y : E, (∃ b : B, b.val = y) →
        ∃ c : A, c.val = Algebra.trace L E (x * y)) ↔
      ∃ b : B, b.val * (a.val : E)⁻¹ = x
    rw [htrace]
    have hbound : ‖x * a.val‖ ≤ 1 ↔ ‖x‖ ≤ q ^ d := by
      rw [norm_mul, ha, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hq d), one_mul]
    constructor
    · intro hx
      exact ⟨⟨x * a.val, (finitePlaceInteger_mem_iff_norm F v _).mpr (hbound.mpr hx)⟩,
        by simp [ha₀]⟩
    · rintro ⟨b, hb⟩
      apply hbound.mp
      have he : x * a.val = b.val := by rw [← hb, mul_assoc, inv_mul_cancel₀ ha₀, mul_one]
      rw [he]
      exact (finitePlaceInteger_mem_iff_norm F v _).mp b.property
  change differentIdeal A B = Ideal.span {a}
  apply FractionalIdeal.coeIdeal_injective (K := E)
  change (↑(differentIdeal A B) : FractionalIdeal B⁰ E) =
    (↑(Ideal.span {a}) : FractionalIdeal B⁰ E)
  rw [coeIdeal_differentIdeal A L E B, hdual, FractionalIdeal.spanSingleton_inv,
    inv_inv, FractionalIdeal.coeIdeal_span_singleton]
  rfl

private theorem finitePlaceIntegerUniformizer_span :
    Ideal.span {finitePlaceIntegerUniformizer F v} = IsLocalRing.maximalIdeal (O F v) := by
  let V : Valuation (K F v) (WithZero (Multiplicative ℤ)) := Valued.v
  have hV : V.Integers (O F v) := Valuation.valuationSubring.integers V
  have hπ : V (finitePlaceIntegerUniformizer F v).val = WithZero.exp (-1 : ℤ) :=
    (chosenFiniteUniformizer_spec F v).trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (HeightOneSpectrum.valuedAdicCompletion_surjective F v)))
  apply SetLike.coe_injective
  rw [hV.coe_span_singleton_eq_setOfPred_le_v_algebraMap (finitePlaceIntegerUniformizer F v)]
  ext x
  change V x.val ≤ V (finitePlaceIntegerUniformizer F v).val ↔
    x ∈ IsLocalRing.maximalIdeal (O F v)
  have hmax : x ∈ IsLocalRing.maximalIdeal (O F v) ↔ V x.val < 1 :=
    Valuation.mem_maximalIdeal_iff (K F v) V
  rw [hmax, hπ]
  have h : V x.val < (WithZero.exp (-1 : ℤ)) * WithZero.exp (1 : ℤ) ↔
      V x.val ≤ WithZero.exp (-1 : ℤ) := WithZero.lt_mul_exp_iff_le (by simp)
  simpa only [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] using h.symm

/-- The absolute norm of the completed different is the cardinality of its
quotient ring. It equals the residue cardinality raised to the global
different exponent at the place. -/
theorem finitePlaceCompletedDifferent_quotientCard :
    Nat.card (O F v ⧸ finitePlaceCompletedDifferent F v) =
      v.asIdeal.absNorm ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) := by
  let B := O F v
  let π := finitePlaceIntegerUniformizer F v
  have hπ : π ≠ 0 := fun h ↦ (chosenFiniteUniformizer F v).ne_zero (congrArg Subtype.val h)
  let H (n : ℕ) := (Ideal.span ({π ^ n} : Set B)).toAddSubgroup
  have h0 : H 0 = ⊤ := by ext x; simp [H]
  have h1 : (H 1).index = v.asIdeal.absNorm := by
    change Nat.card (B ⧸ Ideal.span ({π ^ 1} : Set B)) = _
    rw [pow_one, finitePlaceIntegerUniformizer_span]
    exact finitePlaceResidue_card v
  have hmap (n k : ℕ) : (H k).map (AddMonoidHom.mulLeft (π ^ n)) = H (n + k) := by
    ext x
    change (∃ y ∈ Ideal.span ({π ^ k} : Set B), π ^ n * y = x) ↔
      x ∈ Ideal.span ({π ^ (n + k)} : Set B)
    simp only [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, by rw [pow_add]; ac_rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b * π ^ k, ⟨b, rfl⟩, by rw [pow_add]; ac_rfl⟩
  have hstep (n : ℕ) : (H (n + 1)).index = (H 1).index * (H n).index := by
    let m := AddMonoidHom.mulLeft (π ^ n)
    have hm : Injective m := mul_right_injective₀ (pow_ne_zero _ hπ)
    have h := AddSubgroup.relIndex_map_map_of_injective (f := m) (H 1) (H 0) hm
    rw [hmap, hmap, add_zero, h0, AddSubgroup.relIndex_top_right] at h
    have hle : H (n + 1) ≤ H n := by
      intro x hx
      change x ∈ Ideal.span ({π ^ (n + 1)} : Set B) at hx
      change x ∈ Ideal.span ({π ^ n} : Set B)
      rw [Ideal.mem_span_singleton, pow_succ] at hx
      exact Ideal.mem_span_singleton.mpr ((dvd_mul_right _ _).trans hx)
    rw [← h, AddSubgroup.relIndex_mul_index hle]
  rw [finitePlaceCompletedDifferent_eq_span]
  suffices h : ∀ n, (H n).index = v.asIdeal.absNorm ^ n by exact h _
  intro n
  induction n with
  | zero => rw [h0, AddSubgroup.index_top, pow_zero]
  | succ n ih => rw [hstep, h1, ih, pow_succ, mul_comm]

section Integral

variable [MeasurableSpace (K F v)] [BorelSpace (K F v)]

/-- The local Fourier integral with the positive sign of the adelic pairing. -/
def finitePlaceTraceFourier (ν : Measure (K F v)) (f : K F v → ℂ) (y : K F v) : ℂ :=
  ∫ x, f x * ((finitePlaceTraceCharacter F v (x * y)).toMul : ℂ) ∂ν

theorem finitePlaceTraceFourier_subgroup (ν : Measure (K F v)) [ν.IsAddHaarMeasure]
    (D : AddSubgroup (K F v)) (hD : MeasurableSet (D : Set (K F v))) :
    finitePlaceTraceFourier F v ν ((D : Set (K F v)).indicator (fun _ ↦ (1 : ℂ))) =
      fun y ↦ (ν.real D : ℂ) *
        {y | ∀ x ∈ D, finitePlaceTraceCharacter F v (x * y) = 0}.indicator
          (fun _ ↦ (1 : ℂ)) y := by
  funext y
  let φ (x : K F v) := ((finitePlaceTraceCharacter F v (x * y)).toMul : ℂ)
  let g := (D : Set (K F v)).indicator φ
  change (∫ x, (D : Set (K F v)).indicator (fun _ ↦ (1 : ℂ)) x * φ x ∂ν) = _
  simp_rw [← Set.indicator_mul_left, one_mul]
  change (∫ x, g x ∂ν) = _
  by_cases hy : y ∈ {y | ∀ x ∈ D, finitePlaceTraceCharacter F v (x * y) = 0}
  · rw [indicator_of_mem hy, mul_one]
    change (∫ x, (D : Set (K F v)).indicator φ x ∂ν) = _
    rw [integral_indicator hD]
    have hφ : ∀ x ∈ D, φ x = 1 := fun x hx ↦ by
      have h := hy x hx
      change ((finitePlaceTraceCharacter F v (x * y)).toMul : ℂ) = 1
      rw [h]
      exact Circle.coe_one
    rw [setIntegral_congr_fun hD hφ, setIntegral_const, Complex.real_smul, mul_one]
  · obtain ⟨a, ha, hψ⟩ := not_forall₂.mp hy
    rw [indicator_of_notMem hy, mul_zero]
    have hne : φ a ≠ 1 := fun h ↦ hψ
      (Additive.toMul.injective (Circle.coe_injective (h.trans Circle.coe_one.symm)))
    have hφ (x : K F v) : φ (a + x) = φ a * φ x := by
      dsimp only [φ]
      rw [add_mul, map_add]
      exact Circle.coe_mul _ _
    have ht (x : K F v) : g (a + x) = φ a * g x := by
      have hm : a + x ∈ D ↔ x ∈ D := D.add_mem_cancel_left ha
      by_cases hx : x ∈ D
      · simp only [g, indicator_of_mem hx, indicator_of_mem (hm.mpr hx), hφ]
      · simp only [g, indicator_of_notMem hx, indicator_of_notMem (mt hm.mp hx), mul_zero]
    have he : φ a * (∫ x, g x ∂ν) = 1 * (∫ x, g x ∂ν) := by
      rw [one_mul, ← integral_const_mul, ← integral_add_left_eq_self (μ := ν) g a]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (ht x).symm)
    exact (mul_eq_mul_right_iff.mp he).resolve_left hne

/-- Fourier transformation sends the integer-ring test to its annihilator
indicator times the additive Haar mass of the integer ring. -/
theorem finitePlaceTraceFourier_integerRing (ν : Measure (K F v)) [ν.IsAddHaarMeasure] :
    finitePlaceTraceFourier F v ν ((O F v : Set (K F v)).indicator (fun _ ↦ (1 : ℂ))) =
      fun y ↦ (ν.real (O F v) : ℂ) *
        (finitePlaceIntegerAnnihilator F v).indicator (fun _ ↦ (1 : ℂ)) y :=
  finitePlaceTraceFourier_subgroup F v ν (O F v).toAddSubgroup
    (Valued.isOpen_valuationSubring _).measurableSet

/-- The Fourier transform of the integer-ring test is the indicator of an
actual valuation ball, scaled by the additive Haar mass of the integer ring. -/
theorem finitePlaceTraceFourier_integerRing_ball (ν : Measure (K F v)) [ν.IsAddHaarMeasure] :
    ∃ n : ℤ, finitePlaceTraceFourier F v ν (finiteCompletionIntegerRingTest F v).val =
      fun y ↦ (ν.real (O F v) : ℂ) *
        {u : K F v | ‖u‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)}.indicator (fun _ ↦ (1 : ℂ)) y := by
  obtain ⟨n, hn⟩ := finitePlaceIntegerAnnihilator_eq_ball F v
  refine ⟨n, ?_⟩
  rw [show (finiteCompletionIntegerRingTest F v).val =
    (O F v : Set (K F v)).indicator (fun _ ↦ (1 : ℂ)) from rfl,
    finitePlaceTraceFourier_integerRing, hn]

omit [BorelSpace (K F v)] in
/-- Rescale additive Haar measure to the mass prescribed by the intrinsic
conductor. -/
theorem exists_finitePlace_conductorHaar (ν₀ : Measure (K F v)) [ν₀.IsAddHaarMeasure] :
    ∃ (n : ℤ) (ν : Measure (K F v)), ν.IsAddHaarMeasure ∧
      finitePlaceIntegerAnnihilator F v =
        {y : K F v | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)} ∧
      ν.real (O F v) = Real.exp ((n : ℝ) / 2 * Real.log (v.asIdeal.absNorm : ℝ)) := by
  obtain ⟨n, hn⟩ := finitePlaceIntegerAnnihilator_eq_ball F v
  have hO : IsOpen (O F v : Set (K F v)) := Valued.isOpen_valuationSubring _
  have hcompact : IsCompact (O F v : Set (K F v)) := finitePlaceIntegral_compact F v
  have hm : 0 < ν₀.real (O F v) :=
    ENNReal.toReal_pos (hO.measure_pos ν₀ ⟨0, zero_mem _⟩).ne' hcompact.measure_lt_top.ne
  let m := Real.exp ((n : ℝ) / 2 * Real.log (v.asIdeal.absNorm : ℝ))
  have hm₀ : 0 < m := Real.exp_pos _
  let c := ENNReal.ofReal (m / ν₀.real (O F v))
  have hp : 0 < m / ν₀.real (O F v) := div_pos hm₀ hm
  refine ⟨n, c • ν₀, Measure.IsAddHaarMeasure.smul ν₀
    (by exact (ENNReal.ofReal_pos.mpr hp).ne') ENNReal.ofReal_ne_top, hn, ?_⟩
  change (c • ν₀).real (O F v) = m
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hp.le, div_mul_cancel₀ _ hm.ne']

/-- At the conductor normalization, the positive-sign Fourier transform
applied twice fixes the integer-ring test. -/
theorem finitePlaceTraceFourier_twice_integerRing (ν : Measure (K F v)) [ν.IsAddHaarMeasure]
    (n : ℤ) (hn : finitePlaceIntegerAnnihilator F v =
      {y : K F v | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)})
    (hν : ν.real (O F v) = Real.exp ((n : ℝ) / 2 * Real.log (v.asIdeal.absNorm : ℝ))) :
    let φ := (finiteCompletionIntegerRingTest F v).val
    finitePlaceTraceFourier F v ν (finitePlaceTraceFourier F v ν φ) = φ := by
  intro φ
  let a := chosenFiniteUniformizer F v ^ n
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  let D := (O F v).toAddSubgroup.map (AddMonoidHom.mulLeft a.val)
  have hnorm : ‖a.val‖ = q ^ (-n) := finitePlaceUniformizer_norm_zpow F v n
  have hm (y : K F v) : ‖a.val * y‖ ≤ q ^ (-n) ↔ ‖y‖ ≤ 1 := by
    rw [norm_mul, hnorm]
    conv_lhs => rhs; rw [← mul_one (q ^ (-n))]
    exact mul_le_mul_iff_right₀ (zpow_pos hq (-n))
  have hD : (D : Set (K F v)) = finitePlaceIntegerAnnihilator F v := by
    rw [hn]
    ext y
    change (∃ x ∈ (O F v : Set (K F v)), a.val * x = y) ↔ ‖y‖ ≤ q ^ (-n)
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hm x).mpr ((finitePlaceInteger_mem_iff_norm F v x).mp hx)
    · intro hy
      have he : a.val * (y / a.val) = y := by rw [mul_comm, div_mul_cancel₀ _ a.ne_zero]
      exact ⟨y / a.val, (finitePlaceInteger_mem_iff_norm F v _).mpr
        ((hm _).mp (by rwa [he])), he⟩
  have hAnn : {y | ∀ x ∈ D, finitePlaceTraceCharacter F v (x * y) = 0} =
      (O F v : Set (K F v)) := by
    ext y
    change (∀ x ∈ D, finitePlaceTraceCharacter F v (x * y) = 0) ↔ _
    have he : (∀ x ∈ D, finitePlaceTraceCharacter F v (x * y) = 0) ↔
        a.val * y ∈ finitePlaceIntegerAnnihilator F v := by
      constructor
      · intro h x hx
        have h' := h (a.val * x) (show a.val * x ∈ D from ⟨x, hx, rfl⟩)
        rwa [mul_comm a.val x, mul_assoc] at h'
      · intro h x hx
        obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hx
        change finitePlaceTraceCharacter F v ((a.val * u) * y) = 0
        rw [mul_comm a.val u, mul_assoc]
        exact h u hu
    rw [he, hn, finitePlaceInteger_mem_iff_norm]
    exact hm y
  have hDm : MeasurableSet (D : Set (K F v)) := by
    rw [hD, hn]
    exact (isClosed_le continuous_norm continuous_const).measurableSet
  have hscale : ν.real D = q ^ (-n) * ν.real (O F v) := by
    have he : (D : Set (K F v)) = a • (O F v : Set (K F v)) := rfl
    simp only [measureReal_def, he, finitePlace_addHaar_smul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, coe_nnnorm, hnorm]
  have hmass : ν.real (O F v) * ν.real D = 1 := by
    rw [hscale, hν]
    change Real.exp ((n : ℝ) / 2 * Real.log q) *
      (q ^ (-n) * Real.exp ((n : ℝ) / 2 * Real.log q)) = 1
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hq, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    apply congrArg Real.exp
    push_cast
    ring
  have hφ : φ = ((O F v : Set (K F v)).indicator (fun _ ↦ (1 : ℂ))) := rfl
  rw [hφ, finitePlaceTraceFourier_integerRing, ← hD]
  funext y
  unfold finitePlaceTraceFourier
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  change (ν.real (O F v) : ℂ) *
    finitePlaceTraceFourier F v ν ((D : Set (K F v)).indicator (fun _ ↦ (1 : ℂ))) y = _
  rw [finitePlaceTraceFourier_subgroup F v ν D hDm, hAnn]
  dsimp only
  rw [← mul_assoc, ← Complex.ofReal_mul, hmass, Complex.ofReal_one, one_mul]

variable [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]

omit [MeasurableSpace (K F v)] [BorelSpace (K F v)] in
private theorem finiteZeta_ball_dilate_integral (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (n : ℤ) (z : ℂ) (hz : 0 < z.re) :
    (∫ u : (K F v)ˣ in {u | ‖u.val‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)},
        finiteZetaWeight F v z u ∂μ) =
      Complex.exp (-(n : ℂ) * z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) *
        ((μ.real (finitePlaceIntegralUnits F v) : ℂ) *
          (1 - Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)))⁻¹) := by
  let a := chosenFiniteUniformizer F v ^ n
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  let B : Set (K F v)ˣ := {u | ‖u.val‖ ≤ q ^ (-n)}
  let U : Set (K F v)ˣ := {u | ‖u.val‖ ≤ 1}
  let e := MeasurableEquiv.mulLeft a
  have ha : ‖a.val‖ = q ^ (-n) := finitePlaceUniformizer_norm_zpow F v n
  have he : e ⁻¹' B = U := by
    ext u
    change ‖(a * u).val‖ ≤ q ^ (-n) ↔ ‖u.val‖ ≤ 1
    rw [Units.val_mul, norm_mul, ha]
    conv_lhs => rhs; rw [← mul_one (q ^ (-n))]
    exact mul_le_mul_iff_right₀ (zpow_pos hq (-n))
  have hI := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    e.measurableEmbedding (finiteZetaWeight F v z) B
  change (∫ u in e ⁻¹' B, finiteZetaWeight F v z (a * u) ∂μ) =
    ∫ u in B, finiteZetaWeight F v z u ∂μ at hI
  rw [he] at hI
  change (∫ u in B, finiteZetaWeight F v z u ∂μ) = _
  rw [← hI]
  have hc (u : (K F v)ˣ) :
      finiteZetaWeight F v z (a * u) =
        Complex.exp (-(n : ℂ) * z * (Real.log q : ℂ)) * finiteZetaWeight F v z u := by
    unfold finiteZetaWeight
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr a.ne_zero)
      (norm_ne_zero_iff.mpr u.ne_zero), ha, Real.log_zpow, Complex.ofReal_add,
      mul_add, Complex.exp_add, Complex.ofReal_mul]
    push_cast
    congr 2
    ring
  simp_rw [hc]
  rw [integral_const_mul]
  exact congrArg (_ * ·) (finiteZeta_unitBall_integral F v μ z hz).2

omit [MeasurableSpace (K F v)] [BorelSpace (K F v)]
    [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The unramified local epsilon factor in terms of the signed exponent
of the annihilator ball. -/
def finitePlaceUnramifiedEpsilon (n : ℤ) (s : ℂ) : ℂ :=
  Complex.exp (-(n : ℂ) * (s - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))

omit [MeasurableSpace (K F v)] [BorelSpace (K F v)]
    [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
theorem finitePlaceUnramifiedEpsilon_properties (n : ℤ) :
    Differentiable ℂ (finitePlaceUnramifiedEpsilon F v n) ∧
      (∀ s, finitePlaceUnramifiedEpsilon F v n s ≠ 0) ∧
      ∀ s : ℂ, s.re = 1 / 2 → ‖finitePlaceUnramifiedEpsilon F v n s‖ = 1 := by
  refine ⟨?_, fun s ↦ Complex.exp_ne_zero _, fun s hs ↦ ?_⟩
  · unfold finitePlaceUnramifiedEpsilon
    fun_prop
  · rw [finitePlaceUnramifiedEpsilon, Complex.norm_exp, Real.exp_eq_one_iff]
    have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero,
      Complex.sub_re, hhalf, hs, sub_self, Complex.neg_im, Complex.intCast_im, neg_zero, zero_mul]

/-- The unramified integer-ring calculation on the strip where both zeta
integrals converge. The conductor is the integer defining the actual
annihilator ball. The additive mass is the conductor normalization. -/
theorem finitePlace_normalized_unramified_integerRing
    (ν : Measure (K F v)) [ν.IsAddHaarMeasure]
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (n : ℤ) (hn : finitePlaceIntegerAnnihilator F v =
      {y : K F v | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)})
    (hν : ν.real (O F v) =
      Real.exp ((n : ℝ) / 2 * Real.log (v.asIdeal.absNorm : ℝ)))
    (s : ℂ) (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    let q := (v.asIdeal.absNorm : ℝ)
    let e (z : ℂ) := 1 - Complex.exp (-z * (Real.log q : ℂ))
    let φ := (finiteCompletionIntegerRingTest F v).val
    e s * (∫ u : (K F v)ˣ, φ u.val * finiteZetaWeight F v s u ∂μ) =
      finitePlaceUnramifiedEpsilon F v n s *
        (e (1 - s) * ∫ u : (K F v)ˣ,
          finitePlaceTraceFourier F v ν φ u.val * finiteZetaWeight F v (1 - s) u ∂μ) := by
  intro q e φ
  let C := μ.real (finitePlaceIntegralUnits F v)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hne (z : ℂ) (hz : 0 < z.re) : e z ≠ 0 := by
    have h : ‖Complex.exp (-z * (Real.log q : ℂ))‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hz) (Real.log_pos hq)
    exact sub_ne_zero.mpr fun h' ↦ (by rw [← h', norm_one] at h; exact (lt_irrefl _ h))
  have hdual : 0 < (1 - s).re := by simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hs₁
  have hφ : φ = ((O F v : Set (K F v)).indicator (fun _ ↦ (1 : ℂ))) := rfl
  let U : Set (K F v)ˣ := {u | ‖u.val‖ ≤ 1}
  have hU : MeasurableSet U :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  have hI (z : ℂ) :
      (∫ u : (K F v)ˣ, φ u.val * finiteZetaWeight F v z u ∂μ) =
        ∫ u in U, finiteZetaWeight F v z u ∂μ := by
    rw [← integral_indicator hU]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    change φ u.val * finiteZetaWeight F v z u = U.indicator (finiteZetaWeight F v z) u
    rw [hφ]
    have hm : u.val ∈ (O F v : Set (K F v)) ↔ u ∈ U :=
      finitePlaceInteger_mem_iff_norm F v u.val
    by_cases h : u ∈ U
    · rw [indicator_of_mem (hm.mpr h), indicator_of_mem h, one_mul]
    · rw [indicator_of_notMem (mt hm.mp h), indicator_of_notMem h, zero_mul]
  have hF : finitePlaceTraceFourier F v ν φ = fun y ↦ (ν.real (O F v) : ℂ) *
      {y : K F v | ‖y‖ ≤ q ^ (-n)}.indicator (fun _ ↦ (1 : ℂ)) y := by
    rw [hφ, finitePlaceTraceFourier_integerRing, hn]
  let V : Set (K F v)ˣ := {u | ‖u.val‖ ≤ q ^ (-n)}
  have hV : MeasurableSet V :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  have hIf :
      (∫ u : (K F v)ˣ, finitePlaceTraceFourier F v ν φ u.val * finiteZetaWeight F v (1 - s) u ∂μ) =
        (ν.real (O F v) : ℂ) * ∫ u in V, finiteZetaWeight F v (1 - s) u ∂μ := by
    rw [← integral_const_mul, ← integral_indicator hV]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    change finitePlaceTraceFourier F v ν φ u.val * finiteZetaWeight F v (1 - s) u =
      V.indicator (fun u ↦ (ν.real (O F v) : ℂ) * finiteZetaWeight F v (1 - s) u) u
    rw [hF]
    dsimp only
    have hm : u.val ∈ {y : K F v | ‖y‖ ≤ q ^ (-n)} ↔ u ∈ V := Iff.rfl
    by_cases h : u ∈ V
    · rw [indicator_of_mem (hm.mpr h), indicator_of_mem h, mul_one]
    · rw [indicator_of_notMem (mt hm.mp h), indicator_of_notMem h, mul_zero, zero_mul]
  rw [hI, (finiteZeta_unitBall_integral F v μ s hs₀).2, hIf,
    finiteZeta_ball_dilate_integral F v μ n (1 - s) hdual]
  change e s * ((C : ℂ) * (e s)⁻¹) =
    Complex.exp (-(n : ℂ) * (s - 1 / 2) * (Real.log q : ℂ)) *
      (e (1 - s) * ((ν.real (O F v) : ℂ) *
        (Complex.exp (-(n : ℂ) * (1 - s) * (Real.log q : ℂ)) * ((C : ℂ) * (e (1 - s))⁻¹))))
  have hc : (ν.real (O F v) : ℂ) = Complex.exp ((n : ℂ) / 2 * (Real.log q : ℂ)) := by
    rw [hν, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  rw [hc]
  have he : Complex.exp (-(n : ℂ) * (s - 1 / 2) * (Real.log q : ℂ)) *
      Complex.exp ((n : ℂ) / 2 * (Real.log q : ℂ)) *
      Complex.exp (-(n : ℂ) * (1 - s) * (Real.log q : ℂ)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    apply congrArg Complex.exp
    ring
  trans (C : ℂ)
  · rw [← mul_left_comm (C : ℂ), mul_inv_cancel₀ (hne s hs₀), mul_one]
  · symm
    calc
      _ =
        (Complex.exp (-(n : ℂ) * (s - 1 / 2) * (Real.log q : ℂ)) *
          Complex.exp ((n : ℂ) / 2 * (Real.log q : ℂ)) *
          Complex.exp (-(n : ℂ) * (1 - s) * (Real.log q : ℂ))) *
            (e (1 - s) * (e (1 - s))⁻¹) * (C : ℂ) := by ac_rfl
      _ = _ := by rw [he, mul_inv_cancel₀ (hne (1 - s) hdual), one_mul, one_mul]

end Integral

section Tamagawa

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (K F w)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (K F w)]

/-- The finite factor used in the adelic product has the integer-ring mass
of Definition A.3.1.2 for the actual completed different. -/
theorem additiveHaarDifferent_completedDifferent_mass :
    additiveHaarDifferent F v (O F v) =
      (ENNReal.ofReal (Real.sqrt (Nat.card (O F v ⧸ finitePlaceCompletedDifferent F v) : ℝ)))⁻¹ := by
  rw [additiveHaarDifferent_integers, differentPrimeMass, finitePlaceCompletedDifferent_quotientCard,
    Nat.cast_pow]

/-- The local Tamagawa measure has the mass required by the conductor of the
standard finite-place character. -/
theorem additiveHaarDifferent_conductor_mass :
    (additiveHaarDifferent F v).real (O F v) =
      Real.exp ((-(multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ) : ℝ) /
        2 * Real.log (v.asIdeal.absNorm : ℝ)) := by
  let q := (v.asIdeal.absNorm : ℝ)
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  rw [measureReal_def, additiveHaarDifferent_integers, differentPrimeMass,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  change (Real.sqrt (q ^ d))⁻¹ =
    Real.exp ((-(d : ℤ) : ℝ) / 2 * Real.log q)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le,
    Real.rpow_def_of_pos hq, ← Real.exp_neg]
  push_cast
  congr 1
  ring

/-- Equation (A.3.1.8) with the inverse different expressed by its valuation
ball and the standard finite-place Tamagawa measure. -/
theorem finitePlaceTraceFourier_tamagawa_integerRing :
    let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
    let q := (v.asIdeal.absNorm : ℝ)
    finitePlaceTraceFourier F v (additiveHaarDifferent F v)
      (finiteCompletionIntegerRingTest F v).val =
      fun y ↦ (↑(Real.sqrt (q ^ d)) : ℂ)⁻¹ *
        {x : K F v | ‖x‖ ≤ q ^ d}.indicator (fun _ ↦ (1 : ℂ)) y := by
  intro d q
  letI := additiveHaarDifferent_isHaar F v
  rw [show (finiteCompletionIntegerRingTest F v).val =
    (O F v : Set (K F v)).indicator (fun _ ↦ (1 : ℂ)) from rfl,
    finitePlaceTraceFourier_integerRing, finitePlaceIntegerAnnihilator_eq_differentBall,
    measureReal_def, additiveHaarDifferent_integers, differentPrimeMass,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Complex.ofReal_inv]

/-- The integer-ring test gives the unramified factor of (3.3.1.29) for the
standard character and the Tamagawa Haar measure. -/
theorem finitePlace_tamagawa_unramified_integerRing
    [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (s : ℂ) (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
    let q := (v.asIdeal.absNorm : ℝ)
    let e (z : ℂ) := 1 - Complex.exp (-z * (Real.log q : ℂ))
    let φ := (finiteCompletionIntegerRingTest F v).val
    e s * (∫ u : (K F v)ˣ, φ u.val * finiteZetaWeight F v s u ∂μ) =
      Complex.exp ((d : ℂ) * (s - 1 / 2) * (Real.log q : ℂ)) *
        (e (1 - s) * ∫ u : (K F v)ˣ,
          finitePlaceTraceFourier F v (additiveHaarDifferent F v) φ u.val *
            finiteZetaWeight F v (1 - s) u ∂μ) := by
  intro d q e φ
  letI := additiveHaarDifferent_isHaar F v
  have hn : finitePlaceIntegerAnnihilator F v = {y : K F v | ‖y‖ ≤ q ^ (-(-(d : ℤ)))} := by
    simpa only [neg_neg, zpow_natCast] using finitePlaceIntegerAnnihilator_eq_differentBall F v
  have h := finitePlace_normalized_unramified_integerRing F v (additiveHaarDifferent F v)
    μ (-(d : ℤ)) hn
    (by simpa only [Int.cast_neg, Int.cast_natCast] using additiveHaarDifferent_conductor_mass F v)
    s hs₀ hs₁
  simpa only [finitePlaceUnramifiedEpsilon, Int.cast_neg, Int.cast_natCast, neg_neg] using h

end Tamagawa

end

end Masullo
