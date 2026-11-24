import CoordinatePlaneProductTests
import PointTemperedDistribution
import CompactDistributionTempered
import Mathlib.LinearAlgebra.Multilinear.Basis

open Function Set TopologicalSpace Topology
open scoped ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

private abbrev Tests (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  𝓓((⊤ : Opens E), ℂ)

variable {E D V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private def testDirectionalDerivative (v : E) : Tests E →L[ℂ] Tests E :=
  TestFunction.lineDerivCLM ℂ v

private theorem testDirectionalDerivative_apply (v : E) (f : Tests E) (x : E) :
    testDirectionalDerivative v f x = fderiv ℝ (f : E → ℂ) x v := by
  rw [testDirectionalDerivative, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, ite_eq_left le_top]

private theorem iteratedFDeriv_testDirectionalDerivative (n : ℕ) (v : E) (f : Tests E)
    (x : E) (m : Fin n → E) :
    iteratedFDeriv ℝ n (testDirectionalDerivative v f : E → ℂ) x m =
      iteratedFDeriv ℝ (n+1) (f : E → ℂ) x (Fin.snoc m v) := by
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  let L : (E →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
  have he : (testDirectionalDerivative v f : E → ℂ) = L ∘ fderiv ℝ (f : E → ℂ) := by
    funext y
    exact testDirectionalDerivative_apply v f y
  have hs : ContDiff ℝ (n : ℕ∞ω) (fderiv ℝ (f : E → ℂ)) :=
    f.contDiff.fderiv_right (by exact_mod_cast (le_top : (n : ℕ∞) + 1 ≤ ⊤))
  rw [he, L.iteratedFDeriv_comp_left hs.contDiffAt le_rfl]
  rfl

private def testDirectionalJet : (n : ℕ) → (Fin n → E) → Tests E →L[ℂ] Tests E
  | 0, _ => ContinuousLinearMap.id ℂ _
  | n+1, m => (testDirectionalJet n (Fin.init m)).comp (testDirectionalDerivative (m (Fin.last n)))

private theorem testDirectionalJet_apply (n : ℕ) (m : Fin n → E) (f : Tests E) (x : E) :
    testDirectionalJet n m f x = iteratedFDeriv ℝ n (f : E → ℂ) x m := by
  induction n generalizing f with
  | zero => simp [testDirectionalJet, iteratedFDeriv_zero_apply]
  | succ n ih =>
    change testDirectionalJet n (Fin.init m) (testDirectionalDerivative (m (Fin.last n)) f) x = _
    rw [ih, iteratedFDeriv_testDirectionalDerivative, Fin.snoc_init_self]

private def tangentInclusion : V →ₗᵢ[ℝ] (D × V) where
  toLinearMap := LinearMap.inr ℝ D V
  norm_map' y := by
    change max ‖(0 : D)‖ ‖y‖ = ‖y‖
    rw [norm_zero, max_eq_right (norm_nonneg _)]

section Jets

variable [CompleteSpace V]

/-- Each directional normal jet is a continuous map on the full LF space. -/
def testPlaneNormalJet (n : ℕ) (m : Fin n → D) : Tests (D × V) →L[ℂ] Tests V :=
  (testRestrictLinearIsometry tangentInclusion).comp
    (testDirectionalJet n (fun i ↦ (m i, 0)))

theorem testPlaneNormalJet_apply (n : ℕ) (m : Fin n → D) (f : Tests (D × V)) (y : V) :
    testPlaneNormalJet n m f y =
      iteratedFDeriv ℝ n (f : D × V → ℂ) (0,y) (fun i ↦ (m i, 0)) :=
  testDirectionalJet_apply n _ f (0,y)

end Jets

/-- Extract the coefficient tested by a given normal cutoff. It is supported
in the tangential projection of the compact support of the ambient distribution. -/
theorem testPlaneCoefficient_vanishingOn (T : Tests (D × V) →L[ℂ] ℂ)
    (K : Compacts (D × V))
    (hK : Distribution.IsVanishingOn (⇑T) (K : Set (D × V))ᶜ)
    (φ : Tests D) :
    Distribution.IsVanishingOn (⇑(T.comp (testProductLeft φ)))
      (Prod.snd '' (K : Set (D × V)))ᶜ := by
  intro g hg
  apply hK
  intro z hz hzK
  exact hg ((tsupport_testProductLeft_subset φ g hz).2) ⟨z, hzK, rfl⟩

/-- The distributional support of every extracted coefficient is compact. -/
theorem testPlaneCoefficient_isCompact_dsupport (T : Tests (D × V) →L[ℂ] ℂ)
    (K : Compacts (D × V))
    (hK : Distribution.IsVanishingOn (⇑T) (K : Set (D × V))ᶜ)
    (φ : Tests D) :
    IsCompact (Distribution.dsupport (⇑(T.comp (testProductLeft φ)))) := by
  have hP := K.isCompact.image (f := Prod.snd) continuous_snd
  apply hP.of_isClosed_subset Distribution.isClosed_dsupport
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx _
    (testPlaneCoefficient_vanishingOn T K hK φ) hP.isClosed

/-- A fixed compactly supported normal factor gives a continuous
coefficient distribution of order at most the ambient order. -/
theorem testPlaneCoefficient_orderLE (T : Tests (D × V) →L[ℂ] ℂ)
    (N : ℕ) (hT : testDistributionOrderLE T N) (φ : Tests D) :
    testDistributionOrderLE (T.comp (testProductLeft φ)) N := by
  intro K
  let L : Compacts (D × V) := ⟨tsupport φ ×ˢ (K : Set V), φ.hasCompactSupport.prod K.isCompact⟩
  obtain ⟨C, hC, hbound⟩ := hT L
  let W := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  let A (n : ℕ) : ℝ :=
    ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i W
  let Amax := ∑ n ∈ Finset.range (N+1), A n
  have hA (n : ℕ) : 0 ≤ A n := by dsimp [A]; positivity
  have hAmax : 0 ≤ Amax := Finset.sum_nonneg (fun n _ ↦ hA n)
  refine ⟨C * Amax, mul_nonneg hC hAmax, fun g hg B hB hjet ↦ ?_⟩
  rw [mul_assoc]
  apply hbound (testProductLeft φ g) ((tsupport_testProductLeft_subset φ g).trans
    (fun _ hz ↦ ⟨hz.1, hg hz.2⟩)) _ (mul_nonneg hAmax hB)
  intro n hn z
  change ‖iteratedFDeriv ℝ n (fun x : D × V ↦ φ x.1 * g x.2) z‖ ≤ _
  apply (norm_iteratedFDeriv_separated_mul_le φ.contDiff g.contDiff z n).trans
  calc
    _ ≤ A n * B := by
      dsimp [A]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ W i z.1) (by positivity))
        (hjet _ ((Nat.sub_le _ _).trans hn) z.2) (norm_nonneg _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ ↦ hA k) (Finset.mem_range.mpr (by omega))) hB

/-- For a one-dimensional normal space, the full test-function expansion
is determined by the single jet at each order. The coefficients are
continuous and have compact support in the projected ambient support. -/
theorem realNormal_plane_expansion [CompleteSpace V]
    (T : Tests (ℝ × V) →L[ℂ] ℂ) (N : ℕ) (hT : testDistributionOrderLE T N)
    (hplane : Distribution.IsVanishingOn (⇑T) {x : ℝ × V | x.1 = 0}ᶜ)
    (K : Compacts (ℝ × V))
    (hK : Distribution.IsVanishingOn (⇑T) (K : Set (ℝ × V))ᶜ) :
    ∃ A : Fin (N+1) → (Tests V →L[ℂ] ℂ),
      (∀ k, testDistributionOrderLE (A k) N ∧
        Distribution.IsVanishingOn (⇑(A k)) (Prod.snd '' (K : Set (ℝ × V)))ᶜ) ∧
      (∀ f : Tests (ℝ × V),
        T f = ∑ k, A k (testPlaneNormalJet k.val (fun _ ↦ (1 : ℝ)) f)) := by
  classical
  choose φ hφ using fun k : Fin (N+1) ↦ exists_smoothTest_single_jet k.val
  refine ⟨fun k ↦ T.comp (testProductLeft (φ k)), fun k ↦
    ⟨testPlaneCoefficient_orderLE T N hT _, testPlaneCoefficient_vanishingOn T K hK _⟩, ?_⟩
  intro f
  let U (k : Fin (N+1)) := testPlaneNormalJet k.val (fun _ ↦ (1 : ℝ)) f
  let F := ∑ k, testProductLeft (φ k) (U k)
  have hmatch (y : V) (n : ℕ) (hn : n ≤ N) (m : Fin n → ℝ) :
      iteratedFDeriv ℝ n (f : ℝ × V → ℂ) (0,y) (fun j ↦ (m j, 0)) =
        iteratedFDeriv ℝ n (F : ℝ × V → ℂ) (0,y) (fun j ↦ (m j, 0)) := by
    let k : Fin (N+1) := ⟨n, by omega⟩
    rw [← testPlaneNormalJet_apply n m F y]
    simp only [F, map_sum, sum_apply, testPlaneNormalJet_apply n m,
      testProductLeft_normalJet, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hφ]
    rw [Finset.sum_eq_single k]
    · change _ = ((∏ j, m j) • (if n = n then (1 : ℂ) else 0)) * U k y
      rw [ite_eq_left rfl, smul_mul_assoc, one_mul]
      dsimp only [U]
      rw [testPlaneNormalJet_apply]
      have he (j : Fin n) : (m j, (0 : V)) = m j • ((1 : ℝ), (0 : V)) := by simp
      simp_rw [he]
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    · intro j _ hj
      have hne : n ≠ j.val := fun h ↦ hj (Fin.ext h.symm)
      simp [hne]
    · simp
  rw [productPlane_distribution_eq_of_normal_jets T N hT hplane f F hmatch]
  exact map_sum T _ _

/-- Coordinate-direction probes through degree `N`, with repetition permitted. -/
abbrev PlaneJetIndex (ι : Type*) (N : ℕ) := Σ k : Fin (N + 1), Fin k.val → ι

private def testNormalSlice (f : Tests (D × V)) (y : V) : Tests D := by
  let g (x : D) := f (x, y)
  have hs : support g ⊆ Prod.fst '' tsupport f := by
    intro x hx
    exact ⟨(x,y), subset_tsupport f hx, rfl⟩
  exact ⟨g, f.contDiff.comp (contDiff_id.prodMk contDiff_const),
    (f.hasCompactSupport.image continuous_fst).of_isClosed_subset (isClosed_tsupport g)
      (closure_minimal hs (f.hasCompactSupport.image continuous_fst).isClosed), subset_univ _⟩

private theorem testNormalSlice_jet (f : Tests (D × V)) (y : V) (n : ℕ) (m : Fin n → D) :
    iteratedFDeriv ℝ n (testNormalSlice f y : D → ℂ) 0 m =
      iteratedFDeriv ℝ n (f : D × V → ℂ) (0,y) (fun j ↦ (m j, 0)) := by
  let L := ContinuousLinearMap.inl ℝ D V
  let g (z : D × V) := f (z + (0,y))
  have hg : ContDiff ℝ ∞ g := f.contDiff.comp (contDiff_id.add contDiff_const)
  have he : (testNormalSlice f y : D → ℂ) = g ∘ L := by
    funext x
    change f (x,y) = f ((x, (0 : V)) + (0,y))
    simp
  rw [he]
  rw [L.iteratedFDeriv_comp_right hg _ (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  change iteratedFDeriv ℝ n (fun z : D × V ↦ f (z + (0,y))) (0 : D × V) _ = _
  rw [iteratedFDeriv_comp_add_right, zero_add]
  rfl

set_option maxHeartbeats 1200000 in
/-- The full compact-test expansion in arbitrary finite normal dimension. A
linear section of the finite jet image supplies compactly supported normal
factors, even though the array of coordinate probes has redundant entries. -/
theorem finiteNormal_plane_expansion [CompleteSpace V]
    {D ι : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [Fintype ι]
    (b : Module.Basis ι ℝ D)
    (T : Tests (D × V) →L[ℂ] ℂ) (N : ℕ) (hT : testDistributionOrderLE T N)
    (hplane : Distribution.IsVanishingOn (⇑T) {x : D × V | x.1 = 0}ᶜ)
    (K : Compacts (D × V))
    (hK : Distribution.IsVanishingOn (⇑T) (K : Set (D × V))ᶜ) :
    ∃ A : PlaneJetIndex ι N → (Tests V →L[ℂ] ℂ),
      (∀ k, testDistributionOrderLE (A k) N ∧
        Distribution.IsVanishingOn (⇑(A k)) (Prod.snd '' (K : Set (D × V)))ᶜ) ∧
      ∀ f : Tests (D × V), T f = ∑ k, A k (testPlaneNormalJet k.1.val (b ∘ k.2) f) := by
  classical
  letI : FiniteDimensional ℝ D := Module.Finite.of_basis b
  let I := PlaneJetIndex ι N
  let J : Tests D →ₗ[ℂ] (I → ℂ) :=
    { toFun := fun f k ↦ testDirectionalJet k.1.val (b ∘ k.2) f 0
      map_add' := fun f g ↦ funext fun k ↦ by simp
      map_smul' := fun c f ↦ funext fun k ↦ by simp }
  have hJ (f : Tests D) (k : I) : J f k =
      iteratedFDeriv ℝ k.1.val (f : D → ℂ) 0 (b ∘ k.2) := by
    change testDirectionalJet k.1.val (b ∘ k.2) f 0 = _
    exact testDirectionalJet_apply ..
  obtain ⟨sectionJ, hs⟩ := J.rangeRestrict.exists_rightInverse_of_surjective J.range_rangeRestrict
  obtain ⟨proj, hp⟩ := (LinearMap.range J).subtype.exists_leftInverse_of_injective
    (LinearMap.range J).ker_subtype
  let P : (I → ℂ) →ₗ[ℂ] Tests D := sectionJ.comp proj
  have hP (v : I → ℂ) (hv : v ∈ LinearMap.range J) : J (P v) = v := by
    let z : LinearMap.range J := ⟨v, hv⟩
    have hpr : proj v = z := DFunLike.congr_fun hp z
    exact (congrArg Subtype.val (DFunLike.congr_fun hs (proj v))).trans (congrArg Subtype.val hpr)
  let φ (k : I) := P (Pi.single k 1)
  have hφ (v : I → ℂ) : (∑ k, v k • φ k) = P v := by
    unfold φ
    simp_rw [← map_smul, ← map_sum]
    congr 1
    calc
      (∑ k, v k • Pi.single k (1 : ℂ)) = ∑ k, Pi.single k (v k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      _ = v := LinearMap.sum_single_apply (fun _ ↦ ℂ) v
  refine ⟨fun k ↦ T.comp (testProductLeft (φ k)), fun k ↦
    ⟨testPlaneCoefficient_orderLE T N hT _, testPlaneCoefficient_vanishingOn T K hK _⟩, ?_⟩
  intro f
  let U (k : I) := testPlaneNormalJet k.1.val (b ∘ k.2) f
  let G : Tests (D × V) := ∑ k, testProductLeft (φ k) (U k)
  have hU (y : V) : (fun k ↦ U k y) = J (testNormalSlice f y) := by
    funext k
    rw [hJ, testNormalSlice_jet, show U k y = _ from testPlaneNormalJet_apply ..]
  have hG (y : V) (n : ℕ) (hn : n ≤ N) (m : Fin n → D) :
      iteratedFDeriv ℝ n (f : D × V → ℂ) (0,y) (fun j ↦ (m j, 0)) =
        iteratedFDeriv ℝ n (G : D × V → ℂ) (0,y) (fun j ↦ (m j, 0)) := by
    let L := ContinuousLinearMap.inl ℝ D V
    let A := (iteratedFDeriv ℝ n (f : D × V → ℂ) (0,y)).compContinuousLinearMap (fun _ ↦ L)
    let B := (iteratedFDeriv ℝ n (G : D × V → ℂ) (0,y)).compContinuousLinearMap (fun _ ↦ L)
    change A m = B m
    apply DFunLike.congr_fun (f := A) (g := B) ?_ m
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ ↦ b)
    intro a
    let k : I := ⟨⟨n,by omega⟩, a⟩
    change iteratedFDeriv ℝ n (f : D × V → ℂ) (0,y) (fun j ↦ (b (a j), 0)) =
      iteratedFDeriv ℝ n (G : D × V → ℂ) (0,y) (fun j ↦ (b (a j), 0))
    refine (testPlaneNormalJet_apply n (b ∘ a) f y).symm.trans
      (?_ : U k y = testPlaneNormalJet n (b ∘ a) G y) |>.trans
        (testPlaneNormalJet_apply n (b ∘ a) G y)
    simp only [G, map_sum, sum_apply, testPlaneNormalJet_apply n (b ∘ a),
      testProductLeft_normalJet]
    have h (j : I) : iteratedFDeriv ℝ n (φ j : D → ℂ) 0 (b ∘ a) * U j y =
        J (U j y • φ j) k := by
      rw [map_smul, Pi.smul_apply, hJ, smul_eq_mul, mul_comm]
    have hr : (fun j ↦ U j y) ∈ LinearMap.range J := ⟨testNormalSlice f y, (hU y).symm⟩
    calc
      U k y = J (P (fun j ↦ U j y)) k := (congr_fun (hP _ hr) k).symm
      _ = J (∑ j : I, U j y • φ j) k := congrArg (fun z ↦ J z k) (hφ _).symm
      _ = ∑ j : I, J (U j y • φ j) k := by rw [map_sum, Finset.sum_apply]
      _ = _ := Finset.sum_congr rfl (fun j _ ↦ (h j).symm)
  have he : T f = T G := productPlane_distribution_eq_of_normal_jets T N hT hplane f G hG
  change T f = ∑ k : I, T (testProductLeft (φ k) (U k))
  exact he.trans (map_sum T (fun k : I ↦ testProductLeft (φ k) (U k)) Finset.univ)

/-- A normal multi-index records the multiplicity of each coordinate direction. -/
abbrev PlaneJetMultiIndex (ι : Type*) (N : ℕ) := {m : Multiset ι // m.card ≤ N}

/-- Forget the order of the coordinate probes in a normal derivative. -/
def planeJetMultiplicity {ι : Type*} {N : ℕ} (k : PlaneJetIndex ι N) :
    PlaneJetMultiIndex ι N :=
  ⟨List.ofFn k.2, by simpa using Nat.le_of_lt_succ k.1.isLt⟩

private theorem planeJetMultiplicity_surjective {ι : Type*} {N : ℕ} :
    Surjective (planeJetMultiplicity (ι := ι) (N := N)) := by
  intro m
  have hlen := Multiset.length_toList m.val
  have hdeg : m.val.toList.length < N + 1 := hlen.trans_lt (Nat.lt_succ_of_le m.property)
  refine ⟨⟨⟨m.val.toList.length, hdeg⟩, m.val.toList.get⟩, ?_⟩
  apply Subtype.ext
  change (List.ofFn m.val.toList.get : Multiset ι) = m.val
  rw [List.ofFn_get, Multiset.coe_toList]

noncomputable instance planeJetMultiIndexFintype {ι : Type*} {N : ℕ} [Fintype ι] :
    Fintype (PlaneJetMultiIndex ι N) :=
  haveI := Classical.decEq ι
  Fintype.ofSurjective _ planeJetMultiplicity_surjective

private def planeJetRepresentative {ι : Type*} {N : ℕ} :
    PlaneJetMultiIndex ι N → PlaneJetIndex ι N :=
  surjInv planeJetMultiplicity_surjective

private theorem planeJetRepresentative_spec {ι : Type*} {N : ℕ} (m : PlaneJetMultiIndex ι N) :
    planeJetMultiplicity (planeJetRepresentative m) = m :=
  rightInverse_surjInv planeJetMultiplicity_surjective m

/-- The normal derivative with each chosen coordinate repeated according to its multiplicity. -/
def testPlaneNormalMultiJet [CompleteSpace V] {ι : Type*} (b : Module.Basis ι ℝ D)
    {N : ℕ} (m : PlaneJetMultiIndex ι N) : Tests (D × V) →L[ℂ] Tests V :=
  let k := planeJetRepresentative m
  testPlaneNormalJet k.1.val (b ∘ k.2)

theorem testPlaneNormalMultiJet_eq [CompleteSpace V] {ι : Type*} (b : Module.Basis ι ℝ D)
    {N : ℕ} (k : PlaneJetIndex ι N) (m : PlaneJetMultiIndex ι N)
    (hk : planeJetMultiplicity k = m) :
    testPlaneNormalJet (V := V) k.1.val (b ∘ k.2) = testPlaneNormalMultiJet b m := by
  let j := planeJetRepresentative m
  have hm : planeJetMultiplicity k = planeJetMultiplicity j := hk.trans (planeJetRepresentative_spec m).symm
  have hp : (List.ofFn k.2).Perm (List.ofFn j.2) :=
    Multiset.coe_eq_coe.mp (congrArg Subtype.val hm)
  ext f y
  rw [testPlaneNormalMultiJet, testPlaneNormalJet_apply, testPlaneNormalJet_apply]
  have he := iteratedFDeriv_apply_list_perm f.contDiff (fun i : ι ↦ (b i, (0 : V))) hp (0, y)
  let eval (w : Σ n, Fin n → ι) := iteratedFDeriv ℝ w.1 (f : D × V → ℂ) (0, y)
    (fun i ↦ (b (w.2 i), (0 : V)))
  exact (congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨k.1.val, k.2⟩)).symm.trans
    (he.trans (congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨j.1.val, j.2⟩)))

/-- Grouping ordered coordinate probes by multiplicity gives one coefficient per
normal multi-index. The grouping introduces no new analytic hypotheses. -/
theorem finiteNormal_plane_multiIndex_expansion [CompleteSpace V]
    {D ι : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [Fintype ι]
    (b : Module.Basis ι ℝ D)
    (T : Tests (D × V) →L[ℂ] ℂ) (N : ℕ) (hT : testDistributionOrderLE T N)
    (hplane : Distribution.IsVanishingOn (⇑T) {x : D × V | x.1 = 0}ᶜ)
    (K : Compacts (D × V))
    (hK : Distribution.IsVanishingOn (⇑T) (K : Set (D × V))ᶜ) :
    ∃ A : PlaneJetMultiIndex ι N → (Tests V →L[ℂ] ℂ),
      (∀ m, testDistributionOrderLE (A m) N ∧
        Distribution.IsVanishingOn (⇑(A m)) (Prod.snd '' (K : Set (D × V)))ᶜ) ∧
      ∀ f : Tests (D × V), T f = ∑ m, A m (testPlaneNormalMultiJet b m f) := by
  classical
  obtain ⟨C, hC, he⟩ := finiteNormal_plane_expansion b T N hT hplane K hK
  let A (m : PlaneJetMultiIndex ι N) := ∑ k with planeJetMultiplicity k = m, C k
  refine ⟨A, ?_, ?_⟩
  · intro m
    constructor
    · intro L
      choose M hM hbound using fun k ↦ (hC k).1 L
      let fiber := Finset.univ.filter fun k ↦ planeJetMultiplicity k = m
      refine ⟨∑ k ∈ fiber, M k, Finset.sum_nonneg (fun k _ ↦ hM k), fun g hg B hB hj ↦ ?_⟩
      change ‖(∑ k ∈ fiber, C k) g‖ ≤ (∑ k ∈ fiber, M k) * B
      rw [sum_apply, Finset.sum_mul]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ hbound k g hg B hB hj)
    · intro g hg
      simp only [A, sum_apply]
      exact Finset.sum_eq_zero fun k _ ↦ (hC k).2 g hg
  · intro f
    rw [he f, ← Finset.sum_fiberwise Finset.univ planeJetMultiplicity]
    apply Finset.sum_congr rfl
    intro m _
    simp only [A, sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [testPlaneNormalMultiJet_eq b k m (Finset.mem_filter.mp hk).2]

/-- The distribution obtained by tensoring a normal Dirac derivative with
a tangential coefficient. The sign comes from the distributional transpose. -/
def testPlaneDiracTensor [CompleteSpace V] (n : ℕ) (m : Fin n → D)
    (A : Tests V →L[ℂ] ℂ) : Tests (D × V) →L[ℂ] ℂ :=
  (-1 : ℂ) ^ n • A.comp (testPlaneNormalJet n m)

/-- On a pure tensor the signed coefficient is the signed evaluation
of the normal derivative times the tangential distribution. -/
theorem testPlaneDiracTensor_apply_product [CompleteSpace V] (n : ℕ) (m : Fin n → D)
    (A : Tests V →L[ℂ] ℂ) (φ : Tests D) (g : Tests V) :
    testPlaneDiracTensor n m A (testProductLeft φ g) =
      ((-1 : ℂ) ^ n * iteratedFDeriv ℝ n (φ : D → ℂ) 0 m) * A g := by
  have he : testPlaneNormalJet n m (testProductLeft φ g) =
      iteratedFDeriv ℝ n (φ : D → ℂ) 0 m • g := by
    ext y
    rw [testPlaneNormalJet_apply, testProductLeft_normalJet]
    rfl
  simp only [testPlaneDiracTensor, smul_apply, ContinuousLinearMap.comp_apply, he, map_smul,
    smul_eq_mul, mul_assoc]

/-- A finite normal-jet expansion has the signed distributional tensor form. -/
theorem plane_expansion_eq_sum [CompleteSpace V]
    {ι : Type*} [Fintype ι] (degree : ι → ℕ) (dirs : (k : ι) → Fin (degree k) → D)
    (T : Tests (D × V) →L[ℂ] ℂ) (A : ι → (Tests V →L[ℂ] ℂ))
    (hA : ∀ f : Tests (D × V),
      T f = ∑ k, A k (testPlaneNormalJet (degree k) (dirs k) f)) :
    T = ∑ k, (-1 : ℂ) ^ degree k • testPlaneDiracTensor (degree k) (dirs k) (A k) := by
  ext f
  rw [hA, sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [testPlaneDiracTensor, smul_smul]
  rw [← mul_pow]
  norm_num

/-- The real normal coefficients are uniquely recovered by testing
against the individual cutoff monomials. -/
theorem realNormal_plane_coefficient_apply [CompleteSpace V]
    (T : Tests (ℝ × V) →L[ℂ] ℂ) (N : ℕ) (A : Fin (N+1) → (Tests V →L[ℂ] ℂ))
    (hA : ∀ f : Tests (ℝ × V),
      T f = ∑ j, A j (testPlaneNormalJet j.val (fun _ ↦ (1 : ℝ)) f))
    (k : Fin (N+1)) (φ : Tests ℝ)
    (hφ : ∀ n, iteratedDeriv n (φ : ℝ → ℂ) 0 = if n = k.val then 1 else 0)
    (g : Tests V) :
    A k g = T (testProductLeft φ g) := by
  classical
  have h (j : Fin (N+1)) : testPlaneNormalJet j.val (fun _ ↦ (1 : ℝ))
      (testProductLeft φ g) = (if j = k then (1 : ℂ) else 0) • g := by
    ext y
    rw [testPlaneNormalJet_apply, testProductLeft_normalJet, ← iteratedDeriv_eq_iteratedFDeriv, hφ]
    by_cases hj : j = k
    · subst j
      simp
    · have hn : j.val ≠ k.val := fun h ↦ hj (Fin.ext h)
      simp [hn, hj]
  rw [hA]
  simp only [h, map_smul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private def schwartzDirectionalDerivative (v : E) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  (SchwartzMap.evalCLM ℂ E ℂ v).comp (SchwartzMap.fderivCLM ℂ E ℂ)

private theorem smoothTestToSchwartz_directionalDerivative (v : E) (f : Tests E) :
    smoothTestToSchwartz (testDirectionalDerivative v f) =
      schwartzDirectionalDerivative v (smoothTestToSchwartz f) := by
  ext x
  rw [smoothTestToSchwartz_apply, testDirectionalDerivative_apply]
  rfl

private def schwartzDirectionalJet : (n : ℕ) → (Fin n → E) → 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)
  | 0, _ => ContinuousLinearMap.id ℂ _
  | n+1, m =>
    (schwartzDirectionalJet n (Fin.init m)).comp (schwartzDirectionalDerivative (m (Fin.last n)))

private theorem smoothTestToSchwartz_directionalJet (n : ℕ) (m : Fin n → E) (f : Tests E) :
    smoothTestToSchwartz (testDirectionalJet n m f) =
      schwartzDirectionalJet n m (smoothTestToSchwartz f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change smoothTestToSchwartz
        (testDirectionalJet n (Fin.init m) (testDirectionalDerivative (m (Fin.last n)) f)) =
      schwartzDirectionalJet n (Fin.init m)
        (schwartzDirectionalDerivative (m (Fin.last n)) (smoothTestToSchwartz f))
    rw [ih, smoothTestToSchwartz_directionalDerivative]

/-- Normal differentiation followed by restriction is continuous on the
full Schwartz space. -/
def schwartzPlaneNormalJet (n : ℕ) (m : Fin n → D) : 𝓢(D × V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (schwartzRestrictLinearIsometry tangentInclusion).comp
    (schwartzDirectionalJet n (fun i ↦ (m i, 0)))

/-- The two normal jet maps agree under the compact-test inclusion. -/
theorem smoothTestToSchwartz_planeNormalJet [CompleteSpace V] (n : ℕ) (m : Fin n → D)
    (f : Tests (D × V)) :
    smoothTestToSchwartz (testPlaneNormalJet n m f) =
      schwartzPlaneNormalJet n m (smoothTestToSchwartz f) := by
  ext y
  change (smoothTestToSchwartz (testDirectionalJet n (fun i ↦ (m i, 0)) f)) (0,y) = _
  rw [smoothTestToSchwartz_directionalJet]
  rfl

/-- A compactly supported coordinate-plane expansion extends to
Schwartz tests. Both the ambient and coefficient functionals extend,
and the normal jet identities pass by density. -/
theorem plane_expansion_tempered [FiniteDimensional ℝ D] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] (degree : ι → ℕ) (dirs : (k : ι) → Fin (degree k) → D)
    (T : Tests (D × V) →L[ℂ] ℂ)
    (K : Compacts (D × V)) (hK : Distribution.IsVanishingOn (⇑T) (K : Set (D × V))ᶜ)
    (A : ι → (Tests V →L[ℂ] ℂ))
    (hA : ∀ k, Distribution.IsVanishingOn (⇑(A k)) (Prod.snd '' (K : Set (D × V)))ᶜ)
    (hexp : ∀ f : Tests (D × V),
      T f = ∑ k, A k (testPlaneNormalJet (degree k) (dirs k) f)) :
    ∃ (U : 𝓢(D × V, ℂ) →L[ℂ] ℂ) (B : ι → (𝓢(V, ℂ) →L[ℂ] ℂ)),
      (∀ f : Tests (D × V), U (smoothTestToSchwartz f) = T f) ∧
      (∀ k (f : Tests V), B k (smoothTestToSchwartz f) = A k f) ∧
      U = ∑ k, (B k).comp (schwartzPlaneNormalJet (degree k) (dirs k)) := by
  obtain ⟨U, hU⟩ := exists_temperedExtension_of_compactSupport T K hK
  let P : Compacts V := ⟨Prod.snd '' (K : Set (D × V)), K.isCompact.image continuous_snd⟩
  choose B hB using fun k ↦ exists_temperedExtension_of_compactSupport (A k) P (hA k)
  refine ⟨U, B, hU, hB, ?_⟩
  let C := ∑ k, (B k).comp (schwartzPlaneNormalJet (degree k) (dirs k))
  have he (f : Tests (D × V)) : U (smoothTestToSchwartz f) = C (smoothTestToSchwartz f) := by
    change U (smoothTestToSchwartz f) = (∑ k, (B k).comp
      (schwartzPlaneNormalJet (degree k) (dirs k))) (smoothTestToSchwartz f)
    have hu : U (smoothTestToSchwartz f) = T f := hU f
    rw [sum_apply, hu, hexp]
    apply Finset.sum_congr rfl
    intro k _
    rw [ContinuousLinearMap.comp_apply, ← smoothTestToSchwartz_planeNormalJet]
    exact (hB k _).symm
  ext f
  obtain ⟨g, hg, hlim⟩ := exists_schwartz_compactSupport_sequence f
  have hge (n : ℕ) : U (g n) = C (g n) := by
    let s : Tests (D × V) := ⟨g n, (g n).smooth', hg n, subset_univ _⟩
    have hs : smoothTestToSchwartz s = g n := by ext; rfl
    simpa only [hs] using he s
  exact tendsto_nhds_unique (U.continuous.continuousAt.tendsto.comp hlim)
    ((C.continuous.continuousAt.tendsto.comp hlim).congr (fun n ↦ (hge n).symm))

end
end Masullo
