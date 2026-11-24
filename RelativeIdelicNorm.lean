import AdelicExtension
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Relative norm from the ideles of a number field to the rational ideles

Adapted from `RiemannMasullo/AppA_AlgebraicNT/Sec2.lean` at
cd84b23dd5e4f741037cf31aee06bc90161c6514 under Apache-2.0.
-/

namespace Masullo

noncomputable section

open Filter Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical Pointwise RestrictedProduct

variable (F : Type*) [Field F] [NumberField F]

private abbrev rationalAdeleEmbedding : Adeles ℚ →+* Adeles F := adelesExtension ℚ F

private theorem rationalAdeleEmbedding_fst_eq (a b : Adeles ℚ) (h : a.1 = b.1) :
    (rationalAdeleEmbedding F a).1 = (rationalAdeleEmbedding F b).1 := by
  funext w
  exact congrArg (archCompletionMap ℚ F w) (congrFun h _)

/-- A map into a restricted product is continuous if its coordinates are
continuous and its values share a fixed cofinite set of integral coordinates. -/
private theorem continuous_restrictedProduct_of_uniform {X ι : Type*} [TopologicalSpace X]
    {G : ι → Type*} [∀ i, TopologicalSpace (G i)] {A : (i : ι) → Set (G i)}
    {f : X → Πʳ i, [G i, A i]} (hc : ∀ i, Continuous (fun x ↦ f x i))
    (hA : ∀ᶠ i in cofinite, ∀ x, f x i ∈ A i) : Continuous f := by
  let S := {i | ∀ x, f x i ∈ A i}
  let lift (x : X) : Πʳ i, [G i, A i]_[𝓟 S] := ⟨f x, fun _ hi ↦ hi x⟩
  exact (RestrictedProduct.continuous_inclusion (le_principal_iff.mpr hA)).comp
    ((RestrictedProduct.continuous_rng_of_principal_iff_forall (f := lift)).mpr hc)

/-- Paper: Lemma A.2.2.2, p. 546. The relative idelic norm to the rationals is
the determinant of multiplication on the adele algebra, restricted to units. -/
def relativeIdeleNormRat : Idele F →* Idele ℚ :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  Units.map (Algebra.norm (Adeles ℚ))

section AdeleBasis

local notation "dF(" F ")" => algebraMap F (FiniteAdeleRing (𝓞 F) F)

/-- The finite adeles whose component at every finite place lies in the local integer ring. -/
def finiteIntegralAdeles : Subring (FiniteAdeleRing (𝓞 F) F) :=
  ⨅ v : HeightOneSpectrum (𝓞 F),
    ((v.adicCompletionIntegers F).toSubring).comap (RestrictedProduct.evalRingHom _ v)

local notation "IF(" F ")" => finiteIntegralAdeles F

/-- Membership in the integral finite adeles is tested at each finite place. -/
theorem mem_finiteIntegralAdeles_iff (a : (FiniteAdeleRing (𝓞 F) F)) :
    a ∈ IF(F) ↔ ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F := by
  simp only [finiteIntegralAdeles, Subring.mem_iInf]
  rfl

/-- A diagonal finite adele is integral exactly for field integers. -/
theorem finiteDiagonal_mem_integral (x : F) :
    dF(F) x ∈ IF(F) ↔ ∃ r : 𝓞 F, (r : F) = x := by
  rw [mem_finiteIntegralAdeles_iff]
  exact diagonal_finiteAdeles_integral_iff x

/-- Every finite adele differs from a diagonal field element by an integral finite adele. -/
theorem finiteAdele_sub_diagonal (a : (FiniteAdeleRing (𝓞 F) F)) :
    ∃ x : F, a - dF(F) x ∈ IF(F) := by
  obtain ⟨x, hx⟩ := finiteAdeles_exists_integral_sub_diagonal a
  exact ⟨x, (mem_finiteIntegralAdeles_iff F _).2 hx⟩

theorem isCompact_finiteIntegralAdeles : IsCompact (IF(F) : Set (FiniteAdeleRing (𝓞 F) F)) := by
  let integral (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : (FiniteAdeleRing (𝓞 F) F) :=
    ⟨fun v ↦ x v, Eventually.of_forall fun v ↦ (x v).property⟩
  have hIntegral : Continuous integral :=
    continuous_restrictedProduct_of_uniform
      (fun v ↦ continuous_subtype_val.comp (continuous_apply v))
      (Eventually.of_forall fun v x ↦ (x v).property)
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicIntegers v
  convert isCompact_range hIntegral using 1
  ext a
  rw [SetLike.mem_coe, mem_finiteIntegralAdeles_iff]
  exact ⟨fun ha ↦ ⟨fun v ↦ ⟨a v, ha v⟩, by apply RestrictedProduct.ext; intro v; rfl⟩,
    fun ⟨x, hx⟩ v ↦ hx ▸ (x v).property⟩

/-- Every integral finite adele is congruent to a diagonal field integer modulo any
positive integer times the integral finite adeles. -/
theorem finiteIntegralAdeles_mod_nat (a : (FiniteAdeleRing (𝓞 F) F)) (ha : a ∈ IF(F))
    (n : ℕ) (hn : n ≠ 0) :
    ∃ (z : 𝓞 F) (u : (FiniteAdeleRing (𝓞 F) F)), u ∈ IF(F) ∧ a = dF(F) (z : F) + (n : (FiniteAdeleRing (𝓞 F) F)) * u := by
  obtain ⟨x, hx⟩ := finiteAdele_sub_diagonal F (dF(F) (n : F)⁻¹ * a)
  let u := dF(F) (n : F)⁻¹ * a - dF(F) x
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h : (n : (FiniteAdeleRing (𝓞 F) F)) * u = a - dF(F) ((n : F) * x) := by
    dsimp [u]
    rw [mul_sub, ← map_natCast (dF(F)) n, ← mul_assoc, ← map_mul, ← map_mul,
      mul_inv_cancel₀ hnF, map_one, one_mul]
  have hz : dF(F) ((n : F) * x) ∈ IF(F) := by
    rw [← sub_sub_cancel a (dF(F) ((n : F) * x)), ← h]
    exact (IF(F)).sub_mem ha ((IF(F)).mul_mem (natCast_mem (IF(F)) n) hx)
  obtain ⟨z, hz⟩ := (finiteDiagonal_mem_integral F _).mp hz
  exact ⟨z, u, hx, by rw [hz, h, add_sub_cancel]⟩

/-- A finite adele divisible by every positive integer within the integral finite adeles is zero. -/
theorem finiteAdele_eq_zero_of_forall_nat_mul (a : (FiniteAdeleRing (𝓞 F) F))
    (h : ∀ n : ℕ, n ≠ 0 → ∃ u : (FiniteAdeleRing (𝓞 F) F), u ∈ IF(F) ∧ a = (n : (FiniteAdeleRing (𝓞 F) F)) * u) :
    a = 0 := by
  apply FiniteAdeleRing.ext
  intro w
  by_contra hw
  let P := w.asIdeal.under ℤ
  have hP : P ≠ ⊥ := Ideal.under_ne_bot ℤ w.ne_bot
  obtain ⟨z, hzP, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  let n := z.natAbs
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hnP : (n : ℤ) ∈ P := by
    rcases Int.natAbs_eq z with he | he
    · rw [show (n : ℤ) = z from he.symm]
      exact hzP
    · have hneg : (n : ℤ) = -z := by
        simpa only [neg_neg] using congrArg Neg.neg he.symm
      rw [hneg]
      exact P.neg_mem hzP
  have hnval : Valued.v (n : w.adicCompletion F) < 1 := by
    rw [← map_natCast (algebraMap F (w.adicCompletion F)),
      show Valued.v (algebraMap F (w.adicCompletion F) (n : F)) = _ from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) _]
    change w.valuation F (n : F) < 1
    have hp : (n : 𝓞 F) ∈ w.asIdeal := by simpa [P, Ideal.under] using hnP
    simpa only [map_natCast] using (w.valuation_lt_one_iff_mem (K := F) (n : 𝓞 F)).2 hp
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.mk0 (Valued.v (a w)) ((Valuation.ne_zero_iff _).mpr hw)
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hnval γ
  obtain ⟨u, hu, he⟩ := h (n ^ k) (pow_ne_zero _ hn)
  have huval : Valued.v (u w) ≤ 1 :=
    (mem_finiteIntegralAdeles_iff F u).mp hu w
  have hwa : a w = (n : w.adicCompletion F) ^ k * u w := by
    let ev : (FiniteAdeleRing (𝓞 F) F) →+* w.adicCompletion F :=
      RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F) w
    have he' := congrArg ev he
    rw [map_mul, map_natCast ev (n ^ k), Nat.cast_pow] at he'
    exact he'
  have hc : Valued.v (a w) ≤ Valued.v (n : w.adicCompletion F) ^ k := by
    rw [hwa, map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le huval
  exact (not_lt_of_ge hc) hk

/-- Every neighborhood of zero in the finite adeles contains a positive
integer multiple of the compact group of integral finite adeles. -/
theorem finiteIntegralAdeles_nat_mul_subset_nhds
    {U : Set (FiniteAdeleRing (𝓞 F) F)} (hU : U ∈ 𝓝 0) :
    ∃ n : ℕ, n ≠ 0 ∧
      (fun a : FiniteAdeleRing (𝓞 F) F => (n : FiniteAdeleRing (𝓞 F) F) * a) ''
        (IF(F) : Set (FiniteAdeleRing (𝓞 F) F)) ⊆ U := by
  let A := FiniteAdeleRing (𝓞 F) F
  let I : Set A := IF(F)
  let J := {n : ℕ // n ≠ 0}
  let D (n : J) : Set A := (fun a : A => (n.val : A) * a) '' I
  letI : T2Space A := inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))
  have hI : IsCompact I := isCompact_finiteIntegralAdeles F
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.mp hU
  have hcover : I \ V ⊆ ⋃ n : J, (D n)ᶜ := by
    intro a ha
    by_contra hn
    have hzero : a = 0 := finiteAdele_eq_zero_of_forall_nat_mul F a (fun n hn' => by
      have hmem : a ∈ D ⟨n, hn'⟩ := by
        by_contra hnot
        exact hn (Set.mem_iUnion.mpr ⟨⟨n, hn'⟩, hnot⟩)
      obtain ⟨u, hu, he⟩ := hmem
      exact ⟨u, hu, he.symm⟩)
    exact ha.2 (hzero.symm ▸ h0V)
  obtain ⟨s, hs⟩ := (hI.diff hV).elim_finite_subcover (fun n : J => (D n)ᶜ)
    (fun n => (hI.image (continuous_const.mul continuous_id)).isClosed.isOpen_compl) hcover
  refine ⟨∏ n ∈ s, n.val, Finset.prod_ne_zero_iff.mpr (fun n _ => n.property), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  apply hVU
  by_contra hn
  have hma : (↑(∏ n ∈ s, n.val) : A) * a ∈ I := (IF(F)).mul_mem (natCast_mem _ _) ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hs ⟨hma, hn⟩)
  obtain ⟨hns, hnD⟩ := Set.mem_iUnion.mp hn
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun n : J => n.val) hns
  apply hnD
  refine ⟨(m : A) * a, (IF(F)).mul_mem (natCast_mem _ _) ha, ?_⟩
  rw [hm, Nat.cast_mul, mul_assoc]

/-- The diagonal integral basis gives unique finite adelic coordinates over the rational finite
adeles for a continuous scalar map preserving diagonals and integrality. -/
private theorem finiteAdele_integralBasis_bijective
    (g : (FiniteAdeleRing (𝓞 ℚ) ℚ) →+* (FiniteAdeleRing (𝓞 F) F)) (hg : Continuous g)
    (hdiag : ∀ x : ℚ, g (dF(ℚ) x) = dF(F) (algebraMap ℚ F x))
    (hint : Set.MapsTo g (IF(ℚ) : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (IF(F) : Set (FiniteAdeleRing (𝓞 F) F))) :
    Bijective (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → (FiniteAdeleRing (𝓞 ℚ) ℚ) ↦
      ∑ i, g (c i) * dF(F) (integralBasis F i)) := by
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let b := integralBasis F
  let φ : (ι → (FiniteAdeleRing (𝓞 ℚ) ℚ)) →+ (FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun c ↦ ∑ i, g (c i) * dF(F) (b i)
      map_zero' := by simp
      map_add' := fun c e ↦ by simp [add_mul, Finset.sum_add_distrib] }
  change Bijective φ
  let S : Set (ι → (FiniteAdeleRing (𝓞 ℚ) ℚ)) := Set.pi Set.univ fun _ ↦ (IF(ℚ) : Set (FiniteAdeleRing (𝓞 ℚ) ℚ))
  have hS (c : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ)) : c ∈ S ↔ ∀ i, c i ∈ IF(ℚ) := by simp [S]
  have hi (c : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hc : c ∈ S) : φ c ∈ IF(F) :=
    sum_mem fun i _ ↦ (IF(F)).mul_mem (hint ((hS c).mp hc i))
      ((finiteDiagonal_mem_integral F _).mpr ⟨RingOfIntegers.basis F i, (integralBasis_apply F i).symm⟩)
  have hd (q : ι → ℚ) : φ (fun i ↦ dF(ℚ) (q i)) = dF(F) (b.equivFun.symm q) := by
    change (∑ i, g (dF(ℚ) (q i)) * dF(F) (b i)) = _
    simp only [hdiag, Module.Basis.equivFun_symm_apply, map_sum, Algebra.smul_def, map_mul]
    rfl
  have hcoords (z : 𝓞 F) (i : ι) : dF(ℚ) (b.equivFun (z : F) i) ∈ IF(ℚ) := by
    apply (finiteDiagonal_mem_integral ℚ _).mpr
    refine ⟨((RingOfIntegers.basis F).repr z i : ℤ), ?_⟩
    simp only [Module.Basis.equivFun_apply, b, integralBasis_repr_apply, map_intCast]
    rfl
  have hc : Continuous φ := by
    change Continuous fun c : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ) ↦ ∑ i, g (c i) * dF(F) (b i)
    exact continuous_finsetSum _ fun i _ ↦ (hg.comp (continuous_apply i)).mul continuous_const
  -- Approximate each coefficient by a rational. A relation forces the resulting
  -- rational combination to be a field integer, so its coefficients are integral.
  have hkernel (c : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hzero : φ c = 0) : c ∈ S := by
    choose q hq using fun i ↦ finiteAdele_sub_diagonal ℚ (c i)
    let u : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ) := fun i ↦ c i - dF(ℚ) (q i)
    have hu : u ∈ S := (hS u).mpr hq
    have he : c = (fun i ↦ dF(ℚ) (q i)) + u := by
      funext i
      exact (add_sub_cancel _ _).symm
    rw [he, map_add, hd, add_eq_zero_iff_eq_neg] at hzero
    obtain ⟨z, hz⟩ := (finiteDiagonal_mem_integral F _).mp
      (hzero ▸ (IF(F)).neg_mem (hi u hu))
    have hqz : b.equivFun (z : F) = q := by rw [hz, LinearEquiv.apply_symm_apply]
    rw [he]
    exact (hS _).mpr fun i ↦ (IF(ℚ)).add_mem (hqz ▸ hcoords z i) (hq i)
  constructor
  · apply (injective_iff_map_eq_zero φ).mpr
    intro c hzero
    funext i
    apply finiteAdele_eq_zero_of_forall_nat_mul ℚ
    intro n hn
    -- Apply the same argument after dividing all coefficients by the given integer.
    let t := dF(ℚ) (n : ℚ)⁻¹
    let u : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ) := fun j ↦ t * c j
    have he : φ u = g t * φ c := by
      change (∑ j, g (t * c j) * dF(F) (b j)) = g t * ∑ j, g (c j) * dF(F) (b j)
      simp only [map_mul, mul_assoc, Finset.mul_sum]
    have hu : φ u = 0 := by rw [he, hzero, mul_zero]
    refine ⟨u i, (hS u).mp (hkernel u hu) i, ?_⟩
    change c i = (n : (FiniteAdeleRing (𝓞 ℚ) ℚ)) * (dF(ℚ) (n : ℚ)⁻¹ * c i)
    rw [← mul_assoc, ← map_natCast (dF(ℚ)) n, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), map_one, one_mul]
  · have : T2Space (FiniteAdeleRing (𝓞 F) F) := by
      change T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F])
      infer_instance
    have hcompact : IsCompact (φ '' S) := by
      apply IsCompact.image _ hc
      exact isCompact_univ_pi fun _ ↦ isCompact_finiteIntegralAdeles ℚ
    have hIntSurj (a : (FiniteAdeleRing (𝓞 F) F)) (ha : a ∈ IF(F)) : a ∈ φ '' S := by
      -- Each congruence class meets the compact image of the integral coefficients.
      -- Intersect these conditions and use separation by positive integer multiples.
      let T (n : {n : ℕ // n ≠ 0}) : Set (FiniteAdeleRing (𝓞 F) F) :=
        (φ '' S) ∩ (fun x ↦ a - x) ⁻¹' ((fun u ↦ (n.val : (FiniteAdeleRing (𝓞 F) F)) * u) '' IF(F))
      have hclosed (n : {n : ℕ // n ≠ 0}) :
          IsClosed ((fun x : (FiniteAdeleRing (𝓞 F) F) ↦ a - x) ⁻¹' ((fun u ↦ (n.val : (FiniteAdeleRing (𝓞 F) F)) * u) '' IF(F))) :=
        ((isCompact_finiteIntegralAdeles F).image (continuous_const.mul continuous_id)).isClosed.preimage
          (continuous_const.sub continuous_id)
      have hdirected : Directed (· ⊇ ·) T := by
        intro n m
        have hsub (k l : {n : ℕ // n ≠ 0}) :
            T ⟨k.val * l.val, mul_ne_zero k.property l.property⟩ ⊆ T k := by
          rintro x ⟨hx, u, hu, he⟩
          exact ⟨hx, (l.val : (FiniteAdeleRing (𝓞 F) F)) * u,
            (IF(F)).mul_mem (natCast_mem _ _) hu, by simpa only [Nat.cast_mul, mul_assoc] using he⟩
        refine ⟨⟨n.val * m.val, mul_ne_zero n.property m.property⟩, hsub n m, ?_⟩
        simpa only [mul_comm n.val m.val] using hsub m n
      have hnonempty (n : {n : ℕ // n ≠ 0}) : (T n).Nonempty := by
        obtain ⟨z, u, hu, he⟩ := finiteIntegralAdeles_mod_nat F a ha n n.property
        let q := b.equivFun (z : F)
        have hp : φ (fun i ↦ dF(ℚ) (q i)) = dF(F) (z : F) := by
          rw [hd, LinearEquiv.symm_apply_apply]
        exact ⟨dF(F) (z : F), ⟨_, (hS _).mpr (hcoords z), hp⟩, u, hu,
          (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he.symm))⟩
      have : Nonempty {n : ℕ // n ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T
        hdirected hnonempty (fun n ↦ hcompact.inter_right (hclosed n))
        (fun n ↦ hcompact.isClosed.inter (hclosed n))
      have hxa : a - x = 0 := finiteAdele_eq_zero_of_forall_nat_mul F _ fun n hn ↦ by
        obtain ⟨_, u, hu, he⟩ := Set.mem_iInter.mp hx ⟨n, hn⟩
        exact ⟨u, hu, he.symm⟩
      exact (sub_eq_zero.mp hxa).symm ▸ (Set.mem_iInter.mp hx ⟨1, one_ne_zero⟩).1
    intro a
    obtain ⟨x, hx⟩ := finiteAdele_sub_diagonal F a
    obtain ⟨u, -, hu⟩ := hIntSurj _ hx
    let q := b.equivFun x
    refine ⟨u + (fun i ↦ dF(ℚ) (q i)), ?_⟩
    rw [map_add, hu, hd, LinearEquiv.symm_apply_apply, sub_add_cancel]
/-- The diagonal integral basis gives unique infinite adelic coordinates over the rational
infinite adeles. -/
private theorem infiniteAdele_integralBasis_bijective :
    Bijective (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ ↦
      ∑ i, (rationalAdeleEmbedding F (c i, 0)).1 *
        algebraMap F (InfiniteAdeleRing F) (integralBasis F i)) := by
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let e : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique InfinitePlace.Completion).trans
      (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph
  have hm : Continuous m := by
    simp only [m]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  let f := rationalAdeleEmbedding F
  let j (r : ℝ) : mixedEmbedding.mixedSpace F := m (f (e.symm r, 0)).1
  have hj : Continuous j :=
    hm.comp (continuous_fst.comp ((adelesExtension_continuous ℚ F).comp (e.symm.continuous.prodMk continuous_const)))
  -- Both continuous real scalar maps agree on the dense rational diagonal.
  have hreal : j = algebraMap ℝ (mixedEmbedding.mixedSpace F) := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer hj
      (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace F))
    funext q
    change j (q : ℝ) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (q : ℝ)
    have hq : e ((algebraMap ℚ (Adeles ℚ) q).1) = (q : ℝ) := by
      change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (algebraMap ℚ Rat.infinitePlace.Completion q) = (q : ℝ)
      simp
    have harg : e.symm (q : ℝ) = (algebraMap ℚ (Adeles ℚ) q).1 := e.symm_apply_eq.mpr hq.symm
    have h := rationalAdeleEmbedding_fst_eq F (e.symm (q : ℝ), 0) (algebraMap ℚ (Adeles ℚ) q) harg
    change m (f (e.symm (q : ℝ), 0)).1 = _
    rw [h, adelesExtension_diagonal ℚ F]
    change m (algebraMap F (InfiniteAdeleRing F) (algebraMap ℚ F q)) = _
    exact DFunLike.congr_fun (Subsingleton.elim
      (m.toRingHom.comp ((algebraMap F (InfiniteAdeleRing F)).comp (algebraMap ℚ F)))
      ((algebraMap ℝ (mixedEmbedding.mixedSpace F)).comp (algebraMap ℚ ℝ))) q
  let b := mixedEmbedding.latticeBasis F
  let p := Equiv.piCongrRight (fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ↦ e.toEquiv)
  have he (c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ) :
      m (∑ i, (f (c i, 0)).1 * algebraMap F (InfiniteAdeleRing F) (integralBasis F i)) =
        b.equivFun.symm (p c) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h : m (f (c i, 0)).1 = algebraMap ℝ (mixedEmbedding.mixedSpace F) (e (c i)) := by
      simpa only [j, e.symm_apply_apply] using congrFun hreal (e (c i))
    rw [map_mul, h, Algebra.smul_def, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      ← mixedEmbedding.latticeBasis_apply]
    rfl
  have hcomp : Bijective (fun (c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ) ↦
      m (∑ i, (f (c i, 0)).1 * algebraMap F (InfiniteAdeleRing F) (integralBasis F i))) :=
    (show (fun (c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ) ↦
        m (∑ i, (f (c i, 0)).1 *
        algebraMap F (InfiniteAdeleRing F) (integralBasis F i))) = b.equivFun.symm ∘ p from
      funext he) ▸ b.equivFun.symm.bijective.comp p.bijective
  exact ⟨fun _ _ h ↦ hcomp.injective (congrArg m h),
    fun y ↦ let ⟨c, hc⟩ := hcomp.surjective (m y); ⟨c, m.injective hc⟩⟩

/-- The diagonal images of the integral basis form a basis over the rational adeles. -/
theorem exists_adelicIntegralBasis :
    letI := (rationalAdeleEmbedding F).toAlgebra
    ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (Adeles ℚ) (Adeles F),
      ∀ i, b i = algebraMap F (Adeles F) (integralBasis F i) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  let f := rationalAdeleEmbedding F
  let g := finiteAdelesExtension ℚ F
  have hg : Continuous g := finiteAdelesExtension_continuous ℚ F
  have hgfin (a : Adeles ℚ) : (f a).2 = g a.2 := rfl
  have hgdiag (x : ℚ) : g (dF(ℚ) x) = dF(F) (algebraMap ℚ F x) :=
    congrArg Prod.snd (adelesExtension_diagonal ℚ F x)
  have hgint : Set.MapsTo g (IF(ℚ) : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (IF(F) : Set (FiniteAdeleRing (𝓞 F) F)) := by
    intro a ha
    apply (mem_finiteIntegralAdeles_iff F _).2
    intro w
    exact finiteCompletionMap_integral ℚ F w ((mem_finiteIntegralAdeles_iff ℚ _).1 ha _)
  have hinf (a : Adeles ℚ) : (f a).1 = (f (a.1, 0)).1 :=
    rationalAdeleEmbedding_fst_eq F a (a.1, 0) rfl
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let v (i : ι) := algebraMap F (Adeles F) (integralBasis F i)
  let φ : (ι → (Adeles ℚ)) →ₗ[Adeles ℚ] (Adeles F) :=
    ∑ i, (LinearMap.proj i).smulRight (v i)
  have hφ (a : ι → (Adeles ℚ)) : φ a = ∑ i, f (a i) * v i := by
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Algebra.smul_def]
    rfl
  let φinf (a : ι → InfiniteAdeleRing ℚ) :=
    ∑ i, (f (a i, 0)).1 * algebraMap F (InfiniteAdeleRing F) (integralBasis F i)
  let φf (a : ι → (FiniteAdeleRing (𝓞 ℚ) ℚ)) := ∑ i, g (a i) * dF(F) (integralBasis F i)
  have hinf' (a : ι → (Adeles ℚ)) : (φ a).1 = φinf (fun i ↦ (a i).1) := by
    rw [hφ]
    let proj : Adeles F →+* InfiniteAdeleRing F := RingHom.fst _ _
    change proj (∑ i, f (a i) * v i) = _
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * (v i).1) (hinf (a i))
  have hfin' (a : ι → (Adeles ℚ)) : (φ a).2 = φf (fun i ↦ (a i).2) := by
    rw [hφ]
    let proj : Adeles F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
    change proj (∑ i, f (a i) * v i) = _
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * (v i).2) (hgfin (a i))
  have hinfbij : Bijective φinf := infiniteAdele_integralBasis_bijective F
  have hfinbij : Bijective φf := finiteAdele_integralBasis_bijective F g hg hgdiag hgint
  have hbij : Bijective φ := by
    constructor
    · intro a b h
      have h1 := hinfbij.injective ((hinf' a).symm.trans ((congrArg Prod.fst h).trans (hinf' b)))
      have h2 := hfinbij.injective ((hfin' a).symm.trans ((congrArg Prod.snd h).trans (hfin' b)))
      exact funext fun i ↦ Prod.ext (congrFun h1 i) (congrFun h2 i)
    · intro a
      obtain ⟨x, hx⟩ := hinfbij.surjective a.1
      obtain ⟨y, hy⟩ := hfinbij.surjective a.2
      refine ⟨fun i ↦ (x i, y i), Prod.ext ?_ ?_⟩
      · exact (hinf' _).trans hx
      · exact (hfin' _).trans hy
  refine ⟨(Pi.basisFun (Adeles ℚ) ι).map (LinearEquiv.ofBijective φ hbij), fun i ↦ ?_⟩
  change φ (Pi.basisFun (Adeles ℚ) ι i) = v i
  rw [Pi.basisFun_apply, hφ, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, map_one, one_mul]
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, map_zero, zero_mul]
  · exact fun h ↦ (h (Finset.mem_univ i)).elim

/-- Paper: Lemma A.2.2.2, p. 546. The adele algebra on which the relative norm
takes a determinant is finite free of the field degree.
Deviation: This sanity check rules out the default determinant on modules without a finite basis. -/
theorem rationalAdeleEmbedding_hasBasis :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Nonempty (Module.Basis (Fin (Module.finrank ℚ F)) (Adeles ℚ) (Adeles F)) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b, -⟩ := exists_adelicIntegralBasis F
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ Fin (Module.finrank ℚ F) :=
    (Fintype.equivFin _).trans (finCongr (Module.finrank_eq_card_basis (integralBasis F)).symm)
  exact ⟨b.reindex e⟩

end AdeleBasis

open scoped RestrictedProduct in

/-- The compact closure of the rational fundamental domain has countably many
rational translates covering the adele ring. -/
private theorem rationalAdele_sigmaCompactSpace : SigmaCompactSpace (Adeles ℚ) := by
  let K (q : ℚ) := closure (signedAdelicDomain (F := ℚ)) + {algebraMap ℚ (Adeles ℚ) q}
  have hcover : ⋃ q, K q = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨q, hq, -⟩ := signedAdelicDomain_existsUnique a
    exact Set.mem_iUnion.mpr ⟨q, a - algebraMap ℚ (Adeles ℚ) q,
      subset_closure hq, _, Set.mem_singleton _, sub_add_cancel _ _⟩
  refine ⟨hcover ▸ isSigmaCompact_iUnion_of_isCompact K fun q => ?_⟩
  exact signedAdelicDomain_isCompact_closure.add isCompact_singleton

theorem relativeIdeleNormRat_continuous : Continuous (relativeIdeleNormRat F) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  letI : SigmaCompactSpace (Adeles ℚ) := rationalAdele_sigmaCompactSpace
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  have : T2Space (Adeles F) := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  -- The finite sum map is continuous and open, so its inverse gives continuous coordinates.
  have hsum : Continuous (fun c ↦ b.equivFun.symm c) := by
    simp only [Module.Basis.equivFun_symm_apply, Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      ((adelesExtension_continuous ℚ F).comp (continuous_apply i)).mul continuous_const
  have hcoords : Continuous b.equivFun :=
    b.equivFun.symm.toEquiv.continuous_symm_iff.mpr
      (b.equivFun.symm.toLinearMap.toAddMonoidHom.isOpenMap_of_sigmaCompact
        b.equivFun.symm.surjective hsum)
  unfold relativeIdeleNormRat
  apply Continuous.units_map
  change Continuous (fun x : (Adeles F) ↦ Algebra.norm (Adeles ℚ) x)
  simp_rw [Algebra.norm_eq_matrix_det b]
  apply Continuous.matrix_det
  refine continuous_matrix fun i j ↦ ?_
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply]
  exact (continuous_apply i).comp (hcoords.comp (continuous_id.mul continuous_const))
section RelativeNorm

local notation "ιF" => Module.Free.ChooseBasisIndex ℤ (𝓞 F)
local notation "dQ" => algebraMap ℚ (Adeles ℚ)
local notation "dL" => algebraMap F (Adeles F)

/-- Diagonal rational coordinates lift to adelic coordinates in the diagonal integral basis. -/
theorem adelicIntegralBasis_sum
    (b : letI := (rationalAdeleEmbedding F).toAlgebra; Module.Basis ιF (Adeles ℚ) (Adeles F))
    (hb : ∀ i, b i = dL (integralBasis F i)) (q : ιF → ℚ) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    (∑ i, dQ (q i) • b i) = dL ((integralBasis F).equivFun.symm q) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [hb, Algebra.smul_def, map_mul]
  exact congrArg (· * dL (integralBasis F i)) (adelesExtension_diagonal ℚ F (q i))

/-- The determinant norm on a diagonal adele is the diagonal of the field norm. -/
private theorem rationalAdeleNorm_diagonal
    (b : letI := (rationalAdeleEmbedding F).toAlgebra; Module.Basis ιF (Adeles ℚ) (Adeles F))
    (hb : ∀ i, b i = dL (integralBasis F i)) (x : F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Algebra.norm (Adeles ℚ) (dL x) = dQ (Algebra.norm ℚ x) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (integralBasis F), RingHom.map_det]
  congr 1
  ext i j
  change (Algebra.leftMulMatrix b (dL x)) i j =
    dQ ((Algebra.leftMulMatrix (integralBasis F) x) i j)
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul]
  let y := x * integralBasis F j
  change b.repr (dL y) i = dQ ((integralBasis F).repr y i)
  have h := adelicIntegralBasis_sum F b hb ((integralBasis F).equivFun y)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h, ← b.equivFun_symm_apply]
  change b.equivFun (b.equivFun.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Projecting the determinant is polynomial in the projected coordinates of the input. -/
private theorem rationalAdeleNorm_eval_sum {K : Type*} [CommRing K]
    (b : letI := (rationalAdeleEmbedding F).toAlgebra; Module.Basis ιF (Adeles ℚ) (Adeles F))
    (p : (Adeles ℚ) →+* K) (c : ιF → (Adeles ℚ)) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    p (Algebra.norm (Adeles ℚ) (∑ i, c i • b i)) =
      (∑ i, p (c i) • (Algebra.leftMulMatrix b (b i)).map p).det := by
  let := (rationalAdeleEmbedding F).toAlgebra
  rw [Algebra.norm_eq_matrix_det b, p.map_det, map_sum]
  congr 1
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.sum_apply, map_sum,
    map_smul, Matrix.smul_apply, smul_eq_mul, map_mul]

/-- A projected determinant identity extends from diagonal elements by density in the
scalar coordinates. The scalar `r` retains the projected coordinates on both sides. -/
private theorem rationalAdeleNorm_compare {K : Type*} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (p : (Adeles ℚ) →+* K) (s : K → (Adeles ℚ)) (hs : Continuous s)
    (hdense : DenseRange (p ∘ dQ))
    (r : (Adeles ℚ)) (hr : ∀ c, r * s (p c) = r * c)
    (n : K → ℝ) (hn : Continuous n) (g : (Adeles F) → ℝ) (hg : Continuous g)
    (hgr : ∀ a, g (rationalAdeleEmbedding F r * a) = g a)
    (hdiag : ∀ x : F, n (p (dQ (Algebra.norm ℚ x))) = g (dL x)) (a : Adeles F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    n (p (Algebra.norm (Adeles ℚ) a)) = g a := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b, hb⟩ := exists_adelicIntegralBasis F
  let z (c : ιF → (Adeles ℚ)) : (Adeles F) := ∑ i, c i • b i
  let P (t : ιF → K) : Matrix ιF ιF K := ∑ i, t i • (Algebra.leftMulMatrix b (b i)).map p
  have hproject (c : ιF → (Adeles ℚ)) : p (Algebra.norm (Adeles ℚ) (z c)) = (P (p ∘ c)).det :=
    rationalAdeleNorm_eval_sum F b p c
  have hreplace (c : ιF → (Adeles ℚ)) : g (z (s ∘ p ∘ c)) = g (z c) := by
    rw [← hgr (z (s ∘ p ∘ c)), ← hgr (z c)]
    change g (r • z (s ∘ p ∘ c)) = g (r • z c)
    simp only [z, Finset.smul_sum, smul_smul, Function.comp_apply, hr]
  have hleft : Continuous (fun t ↦ n (P t).det) := by
    apply hn.comp
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    refine continuous_finsetSum _ fun σ _ ↦ continuous_const.mul
      (continuous_finsetProd _ fun j _ ↦ ?_)
    simp only [P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const
  have hright : Continuous (fun t ↦ g (z (s ∘ t))) := by
    apply hg.comp
    simp only [z, Function.comp_apply, Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      ((adelesExtension_continuous ℚ F).comp (hs.comp (continuous_apply i))).mul
        continuous_const
  have hd : DenseRange (fun q : ιF → ℚ ↦ p ∘ dQ ∘ q) :=
    DenseRange.piMap fun _ ↦ hdense
  have he := hd.equalizer hleft hright (by
    funext q
    change n (P (p ∘ dQ ∘ q)).det = g (z (s ∘ p ∘ dQ ∘ q))
    have hz : z (dQ ∘ q) = dL ((integralBasis F).equivFun.symm q) :=
      adelicIntegralBasis_sum F b hb q
    rw [← hproject (dQ ∘ q), hreplace (dQ ∘ q), hz, rationalAdeleNorm_diagonal F b hb]
    exact hdiag _)
  let c := b.equivFun a
  have hc : z c = a := (b.equivFun_symm_apply c).symm.trans (b.equivFun.symm_apply_apply a)
  calc
    n (p (Algebra.norm (Adeles ℚ) a)) = n (P (p ∘ c)).det := by rw [← hc, hproject]
    _ = g (z (s ∘ p ∘ c)) := congrFun he (p ∘ c)
    _ = g a := (hreplace c).trans (congrArg g hc)

/-- The archimedean factor of the adelic determinant norm agrees with the normalized
archimedean product on the original adele. -/
private theorem rationalAdeleNorm_infinite (a : Adeles F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    ‖(Algebra.norm (Adeles ℚ) a).1‖ = ‖a.1‖ := by
  have hQ : Continuous (fun x : InfiniteAdeleRing ℚ ↦ ‖x‖) := by
    simp only [InfiniteAdeleRing.norm_def]
    exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).norm.pow _
  have hF : Continuous (fun x : InfiniteAdeleRing F ↦ ‖x‖) := by
    simp only [InfiniteAdeleRing.norm_def]
    exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).norm.pow _
  let r : (Adeles ℚ) := (1, 0)
  refine rationalAdeleNorm_compare F (RingHom.fst _ _) (fun t ↦ (t, 0))
    (continuous_id.prodMk continuous_const)
    (InfiniteAdeleRing.denseRange_algebraMap ℚ) r ?_ norm hQ
    (fun a ↦ ‖a.1‖) (hF.comp continuous_fst) ?_ ?_ a
  · intro c
    exact Prod.ext rfl (by change (0 : (FiniteAdeleRing (𝓞 ℚ) ℚ)) * 0 = 0 * c.2; simp)
  · intro x
    change ‖(rationalAdeleEmbedding F r).1 * x.1‖ = ‖x.1‖
    rw [rationalAdeleEmbedding_fst_eq F r 1 rfl, map_one]
    change ‖1 * x.1‖ = ‖x.1‖
    rw [one_mul]
  · intro x
    change ‖algebraMap ℚ (InfiniteAdeleRing ℚ) (Algebra.norm ℚ x)‖ =
      ‖algebraMap F (InfiniteAdeleRing F) x‖
    rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, InfiniteAdeleRing.coe_norm_eq_abs_norm]
    exact congrArg (fun q : ℚ => (↑|q| : ℝ))
      (DFunLike.congr_fun (Algebra.norm_self (R := ℚ)) (Algebra.norm ℚ x))

attribute [local instance] FractionRing.liftAlgebra in
/-- The multiplicity of a rational prime in a relative ideal norm is the sum of the
multiplicities above it, weighted by the inertia degrees. -/
private theorem multiplicity_relNorm_rat (v : HeightOneSpectrum (𝓞 ℚ))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    let s := (Ideal.hasFiniteMulSupport hI).toFinset
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 ℚ) I) =
      ∑ w ∈ s with w.under (𝓞 ℚ) = v, multiplicity w.asIdeal I * w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  let s := (Ideal.hasFiniteMulSupport hI).toFinset
  let N : Ideal (𝓞 F) →*₀ Ideal (𝓞 ℚ) := Ideal.relNorm (𝓞 ℚ)
  let m (w : HeightOneSpectrum (𝓞 F)) := multiplicity w.asIdeal I
  have hpow (w : HeightOneSpectrum (𝓞 F)) :
      N (w.maxPowDividing I) = (w.under (𝓞 ℚ)).asIdeal ^ (m w * w.asIdeal.inertiaDeg (𝓞 ℚ)) := by
    let u := w.under (𝓞 ℚ)
    have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
    have := w.isMaximal
    have := u.isMaximal
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow,
      Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal u.asIdeal, ← pow_mul, Nat.mul_comm]
  have hfac : ∏ w ∈ s, N (w.maxPowDividing I) = N I := by
    rw [← map_prod, ← finprod_eq_prod _ (Ideal.hasFiniteMulSupport hI),
      Ideal.finprod_heightOneSpectrum_factorization hI]
  have hmult (w : HeightOneSpectrum (𝓞 F)) :
      emultiplicity v.asIdeal (N (w.maxPowDividing I)) =
        if w.under (𝓞 ℚ) = v then ((m w * w.asIdeal.inertiaDeg (𝓞 ℚ) : ℕ) : ℕ∞) else 0 := by
    rw [hpow]
    split_ifs with hw
    · rw [hw, emultiplicity_pow_self_of_prime v.prime]
    · have hnd : ¬ v.asIdeal ∣ (w.under (𝓞 ℚ)).asIdeal := by
        intro h
        exact hw (HeightOneSpectrum.ext ((w.under (𝓞 ℚ)).isMaximal.eq_of_le
          v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)))
      rw [emultiplicity_pow v.prime, emultiplicity_eq_zero.mpr hnd, mul_zero]
  have h := (Finset.emultiplicity_prod v.prime s (fun w ↦ N (w.maxPowDividing I))).symm
  rw [hfac, (FiniteMultiplicity.of_prime_left v.prime
    (mt (Ideal.relNorm_eq_bot_iff (R := 𝓞 ℚ)).mp hI)).emultiplicity_eq_multiplicity] at h
  simp only [hmult, ← Finset.sum_filter] at h
  exact_mod_cast h.symm

/-- The normalized norm of an integer at a finite place is the inverse residue
cardinality raised to its multiplicity. -/
private theorem norm_int_finitePlace {K : Type*} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {z : 𝓞 K} (hz : z ≠ 0) :
    ‖algebraMap K (w.adicCompletion K) (z : K)‖ =
      (w.asIdeal.absNorm : ℝ)⁻¹ ^ multiplicity w.asIdeal (Ideal.span {z}) := by
  have h := (FinitePlace.mk w).apply_mul_absNorm_pow_eq_one hz
  rw [FinitePlace.maximalIdeal_mk, FinitePlace.mk_apply] at h
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h

/-- The finite-place norm identity for nonzero field integers. -/
private theorem norm_fieldNorm_ratFinitePlace_int (v : HeightOneSpectrum (𝓞 ℚ))
    {z : 𝓞 F} (hz : z ≠ 0) :
    ‖algebraMap ℚ (v.adicCompletion ℚ) (Algebra.norm ℚ (z : F))‖ =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
        ‖algebraMap F (w.adicCompletion F) (z : F)‖ := by
  let I : Ideal (𝓞 F) := Ideal.span {z}
  have hI : I ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hz
  let y := Algebra.intNorm (𝓞 ℚ) (𝓞 F) z
  have hy : (y : ℚ) = Algebra.norm ℚ (z : F) := Algebra.algebraMap_intNorm z
  have hy0 : y ≠ 0 := by
    intro h
    apply (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hz) : Algebra.norm ℚ (z : F) ≠ 0)
    rw [← hy, h]
    rfl
  rw [← hy, norm_int_finitePlace v hy0, ← Ideal.relNorm_singleton]
  change (v.asIdeal.absNorm : ℝ)⁻¹ ^ multiplicity v.asIdeal (Ideal.relNorm (𝓞 ℚ) I) = _
  rw [multiplicity_relNorm_rat F v I hI]
  let s := (Ideal.hasFiniteMulSupport hI).toFinset
  let p := (v.asIdeal.absNorm : ℝ)⁻¹
  rw [← Finset.prod_pow_eq_pow_sum]
  symm
  have hprod : (∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
      ‖algebraMap F (w.adicCompletion F) (z : F)‖) =
      ∏ w ∈ s with w.under (𝓞 ℚ) = v, ‖algebraMap F (w.adicCompletion F) (z : F)‖ := by
    apply finprod_cond_eq_prod_of_cond_iff
    intro w hw
    rw [Finset.mem_filter]
    refine ⟨fun h ↦ ⟨(Ideal.hasFiniteMulSupport hI).mem_toFinset.mpr ?_, h⟩, And.right⟩
    intro hOne
    apply hw
    change w.maxPowDividing (Ideal.span {z}) = 1 at hOne
    change ‖FinitePlace.embedding w (algebraMap (𝓞 F) F z)‖ = 1
    simpa only [hOne, map_one, Nat.cast_one, mul_one] using
      HeightOneSpectrum.embedding_mul_absNorm F w hz
  rw [hprod]
  apply Finset.prod_congr rfl
  intro w hw
  have huv := (Finset.mem_filter.mp hw).2
  have : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal huv.symm⟩
  have hcard := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  rw [norm_int_finitePlace w hz]
  change (w.asIdeal.absNorm : ℝ)⁻¹ ^ multiplicity w.asIdeal I =
    p ^ (multiplicity w.asIdeal I * w.asIdeal.inertiaDeg (𝓞 ℚ))
  rw [← hcard, Nat.cast_pow, ← inv_pow, ← pow_mul, Nat.mul_comm]

/-- The places of a number field above a fixed rational finite place form a finite set. -/
private theorem finite_finitePlacesOver_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    {w : HeightOneSpectrum (𝓞 F) | w.under (𝓞 ℚ) = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 F)).subset ?_).of_finite_image
    (HeightOneSpectrum.asIdeal_injective.injOn)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩

/-- The absolute value of a field norm at a rational finite prime is the product of
the normalized absolute values of the element at the primes above it. -/
private theorem norm_fieldNorm_ratFinitePlace (v : HeightOneSpectrum (𝓞 ℚ)) (x : F) :
    ‖algebraMap ℚ (v.adicCompletion ℚ) (Algebra.norm ℚ x)‖ =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
        ‖algebraMap F (w.adicCompletion F) x‖ := by
  let s := (finite_finitePlacesOver_rat F v).toFinset
  have hprod (a : F) : (∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
      ‖algebraMap F (w.adicCompletion F) a‖) =
      ∏ w ∈ s, ‖algebraMap F (w.adicCompletion F) a‖ :=
    finprod_mem_eq_finite_toFinset_prod _ (finite_finitePlacesOver_rat F v)
  by_cases hx : x = 0
  · subst x
    have := v.isMaximal
    obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) v.asIdeal
    let w : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
    have hw : w.under (𝓞 ℚ) = v := HeightOneSpectrum.ext hPv.over.symm
    rw [Algebra.norm_zero, map_zero, norm_zero, hprod]
    symm
    exact Finset.prod_eq_zero ((finite_finitePlacesOver_rat F v).mem_toFinset.mpr hw)
      (by rw [map_zero, norm_zero])
  · obtain ⟨z, t, ht, hzt⟩ := IsFractionRing.div_surjective (𝓞 F) x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hz : z ≠ 0 := by
      intro h
      exact hx (by rw [← hzt, h, map_zero, zero_div])
    have hnorm (a b : F) : Algebra.norm ℚ (a / b) = Algebra.norm ℚ a / Algebra.norm ℚ b := by
      simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
    rw [← hzt, hnorm, map_div₀, norm_div, norm_fieldNorm_ratFinitePlace_int F v hz,
      norm_fieldNorm_ratFinitePlace_int F v ht0, hprod, hprod, hprod]
    simp only [map_div₀, norm_div, Finset.prod_div_distrib]


open scoped RestrictedProduct in
/-- At each rational finite place, the adelic determinant has absolute value equal to
the product of the normalized local factors above that place. -/
private theorem rationalAdeleNorm_finitePlace (v : HeightOneSpectrum (𝓞 ℚ)) (a : Adeles F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    ‖(Algebra.norm (Adeles ℚ) a).2 v‖ =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v), ‖a.2 w‖ := by
  let p : (Adeles ℚ) →+* v.adicCompletion ℚ :=
    (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletion ℚ) v).comp
      (RingHom.snd _ _)
  let e : v.adicCompletion ℚ → (FiniteAdeleRing (𝓞 ℚ) ℚ) := fun t ↦ ⟨Pi.single v t, by
    filter_upwards [Filter.eventually_cofinite_ne v] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact (w.adicCompletionIntegers ℚ).zero_mem⟩
  have he : Continuous e := by
    apply continuous_restrictedProduct_of_uniform
    · intro w
      change Continuous (fun t : v.adicCompletion ℚ ↦ Pi.single v t w)
      by_cases hw : w = v
      · subst w
        simp only [Pi.single_eq_same]
        exact continuous_id
      · simp only [Pi.single_eq_of_ne hw]
        exact continuous_const
    · filter_upwards [Filter.eventually_cofinite_ne v] with w hw t
      change Pi.single v t w ∈ w.adicCompletionIntegers ℚ
      rw [Pi.single_eq_of_ne hw]
      exact (w.adicCompletionIntegers ℚ).zero_mem
  let r : (Adeles ℚ) := (0, e 1)
  let g (x : Adeles F) := ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v), ‖x.2 w‖
  have hprod (x : Adeles F) :
      g x = ∏ w ∈ (finite_finitePlacesOver_rat F v).toFinset, ‖x.2 w‖ :=
    finprod_mem_eq_finite_toFinset_prod _ (finite_finitePlacesOver_rat F v)
  have hg : Continuous g := by
    change Continuous (fun x ↦ g x)
    simp only [hprod]
    exact continuous_finsetProd _ fun w _ ↦ ((RestrictedProduct.continuous_eval w).comp
      continuous_snd).norm
  refine rationalAdeleNorm_compare F p (fun t ↦ (0, e t)) (continuous_const.prodMk he)
    (v.denseRange_algebraMap ℚ) r ?_ norm continuous_norm g hg ?_
    (norm_fieldNorm_ratFinitePlace F v) a
  · intro c
    refine Prod.ext ?_ ?_
    · change (0 : InfiniteAdeleRing ℚ) * 0 = 0 * c.1
      simp
    · apply FiniteAdeleRing.ext
      intro w
      change Pi.single v 1 w * Pi.single v (c.2 v) w = Pi.single v 1 w * c.2 w
      by_cases hw : w = v
      · subst w
        simp
      · simp [Pi.single_eq_of_ne hw]
  · intro x
    simp only [hprod]
    apply Finset.prod_congr rfl
    intro w hw
    have h := (finite_finitePlacesOver_rat F v).mem_toFinset.mp hw
    have hf : (rationalAdeleEmbedding F r).2 w = 1 := by
      change finiteCompletionMap ℚ F w (r.2 (w.under (𝓞 ℚ))) = 1
      have he : (r.2 (w.under (𝓞 ℚ))) = 1 := by
        change Pi.single v (1 : v.adicCompletion ℚ) (w.under (𝓞 ℚ)) = 1
        rw [h, Pi.single_eq_same]
      rw [he, map_one]
    change ‖(rationalAdeleEmbedding F r).2 w * x.2 w‖ = ‖x.2 w‖
    rw [hf, one_mul]

/-- The finite product of projected determinant norms is the finite factor
of the idelic norm on the original idele. -/
private theorem relativeIdeleNormRat_finite (a : Idele F) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖(relativeIdeleNormRat F a).val.2 v‖) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖a.val.2 w‖ := by
  let f (w : HeightOneSpectrum (𝓞 F)) := ‖a.val.2 w‖
  have hf : f.HasFiniteMulSupport := finiteIdeleNorm_hasFiniteMulSupport F a
  rw [finprod_eq_prod f hf, ← finprod_prod_filter (HeightOneSpectrum.under (𝓞 ℚ)) hf.toFinset f]
  apply finprod_congr
  intro v
  refine (rationalAdeleNorm_finitePlace F v a.val).trans ?_
  apply finprod_cond_eq_prod_of_cond_iff f
  intro w hw
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨hf.mem_toFinset.mpr hw, h⟩, And.right⟩

/-- Paper: Lemma A.2.2.2, p. 546. Taking the rational idelic norm after the relative
norm gives the idelic norm of the original idele. -/
theorem ideleNorm_comp_relativeIdeleNormRat :
    (ideleNorm ℚ).comp (relativeIdeleNormRat F) = ideleNorm F := by
  apply MonoidHom.ext
  intro a
  change ‖(relativeIdeleNormRat F a).val.1‖ * (∏ᶠ v, ‖(relativeIdeleNormRat F a).val.2 v‖) =
    ‖a.val.1‖ * (∏ᶠ v, ‖a.val.2 v‖)
  rw [relativeIdeleNormRat_finite F a, show ‖(relativeIdeleNormRat F a).val.1‖ = ‖a.val.1‖ from
    rationalAdeleNorm_infinite F a.val]

end RelativeNorm

/-- Trace of multiplication on the actual adelic scalar extension. -/
def relativeAdelicTraceRat : Adeles F →+ Adeles ℚ :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  (Algebra.trace (Adeles ℚ) (Adeles F)).toAddMonoidHom

/-- The trace of a diagonal adele is the diagonal of the field trace. -/
theorem relativeAdelicTraceRat_diagonal (x : F) :
    relativeAdelicTraceRat F (algebraMap F (Adeles F) x) =
      algebraMap ℚ (Adeles ℚ) (Algebra.trace ℚ F x) := by
  letI := (rationalAdeleEmbedding F).toAlgebra
  let j := algebraMap F (Adeles F)
  let j₀ := algebraMap ℚ (Adeles ℚ)
  obtain ⟨b, hb⟩ := exists_adelicIntegralBasis F
  change Algebra.trace (Adeles ℚ) (Adeles F) (j x) = j₀ (Algebra.trace ℚ F x)
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (integralBasis F)]
  unfold Matrix.trace
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (Algebra.leftMulMatrix b (j x)) i i = j₀ ((Algebra.leftMulMatrix (integralBasis F) x) i i)
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul]
  let y := x * integralBasis F i
  change b.repr (j y) i = j₀ ((integralBasis F).repr y i)
  have hh := adelicIntegralBasis_sum F b hb ((integralBasis F).equivFun y)
  rw [LinearEquiv.symm_apply_apply] at hh
  rw [← hh, ← b.equivFun_symm_apply]
  change b.equivFun (b.equivFun.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Linearity of the adelic trace over the rational adeles. -/
theorem relativeAdelicTraceRat_mul_rat (r : Adeles ℚ) (x : Adeles F) :
    relativeAdelicTraceRat F (adelesExtension ℚ F r * x) =
      r * relativeAdelicTraceRat F x := by
  letI := (rationalAdeleEmbedding F).toAlgebra
  change Algebra.trace (Adeles ℚ) (Adeles F) (r • x) =
    r • Algebra.trace (Adeles ℚ) (Adeles F) x
  exact map_smul _ r x

/-- The trace is continuous, by the finite scalar coordinate homeomorphism. -/
theorem relativeAdelicTraceRat_continuous : Continuous (relativeAdelicTraceRat F) := by
  let : Algebra (Adeles ℚ) (Adeles F) := (rationalAdeleEmbedding F).toAlgebra
  have hF : Continuous (algebraMap (Adeles ℚ) (Adeles F)) := adelesExtension_continuous ℚ F
  have : T2Space (Adeles F) := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicIntegers v
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  have : LocallyCompactSpace (Adeles F) := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : SigmaCompactSpace (Adeles ℚ) := rationalAdele_sigmaCompactSpace
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  let e := b.equivFun.symm
  have he : Continuous e := by
    change Continuous (fun a ↦ e a)
    simp only [e, Module.Basis.equivFun_symm_apply, Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      (hF.comp (continuous_apply i)).mul continuous_const
  -- The open mapping theorem gives continuity of the inverse coordinate map.
  have hcoords : Continuous e.symm :=
    e.toEquiv.continuous_symm_iff.mpr (e.toAddMonoidHom.isOpenMap_of_sigmaCompact e.surjective he)
  let tr := Algebra.trace (Adeles ℚ) (Adeles F)
  have htr' : Continuous (fun a ↦ tr (e a)) := by
    simp only [e, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const
  change Continuous tr
  exact (htr'.comp hcoords).congr (fun x ↦ congrArg tr (e.apply_symm_apply x))

/-- The normalized adelic trace gives a continuous retraction of scalar extension
on the adele rings. -/
private theorem rationalAdeleEmbedding_isClosedEmbedding :
    IsClosedEmbedding (rationalAdeleEmbedding F) := by
  let : Algebra (Adeles ℚ) (Adeles F) := (rationalAdeleEmbedding F).toAlgebra
  have hF : Continuous (algebraMap (Adeles ℚ) (Adeles F)) := adelesExtension_continuous ℚ F
  have : T2Space (Adeles F) := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  let tr := Algebra.trace (Adeles ℚ) (Adeles F)
  have htr : Continuous tr := relativeAdelicTraceRat_continuous F
  let d := Module.finrank ℚ F
  let c := algebraMap ℚ (Adeles ℚ) (d : ℚ)⁻¹
  have hleft : LeftInverse (fun x ↦ c * tr x) (algebraMap (Adeles ℚ) (Adeles F)) := by
    intro a
    change c * tr (algebraMap (Adeles ℚ) (Adeles F) a) = a
    rw [Algebra.trace_algebraMap_of_basis b, Fintype.card_fin, nsmul_eq_mul]
    change c * ((d : (Adeles ℚ)) * a) = a
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ (Adeles ℚ)) d, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := F)).ne'),
      map_one, one_mul]
  exact hleft.isClosedEmbedding (continuous_const.mul htr) hF

open scoped RestrictedProduct in
/-- Paper: Lemma A.2.2.2, p. 546. Scalar extension embeds the rational ideles as a
closed subgroup of the ideles of the field. -/
theorem rationalIdeleEmbedding_isClosedEmbedding :
    IsClosedEmbedding (idelesExtension ℚ F) := by
  have : T2Space (Adeles ℚ) := by
    change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  exact (rationalAdeleEmbedding_isClosedEmbedding F).units_map

/-- Paper: Lemma A.2.2.2, p. 546. The relative norm of an extended rational
idele is the original idele raised to the field degree. -/
theorem relativeIdeleNormRat_on_rational (g : Idele ℚ) :
    relativeIdeleNormRat F (idelesExtension ℚ F g) =
      g ^ Module.finrank ℚ F := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  apply Units.ext
  change Algebra.norm (Adeles ℚ) (algebraMap (Adeles ℚ) (Adeles F) g.val) = g.val ^ Module.finrank ℚ F
  simpa only [Fintype.card_fin] using Algebra.norm_algebraMap_of_basis b g.val

end

end Masullo
