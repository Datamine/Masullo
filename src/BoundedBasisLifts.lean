import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.Units

open Filter Function Set Topology

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The prescribed subspace is dense in every quotient fiber it meets. -/
theorem quotient_approximate_in_submodule (N F : Submodule ℂ E) [IsClosed (N : Set E)]
    (hDense : Dense {v : N | (v : E) ∈ F})
    (w : E) (hw : N.mkQ w ∈ N.mkQ '' (F : Set E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ F, N.mkQ u = N.mkQ w ∧ ‖u - w‖ < ε := by
  obtain ⟨v, hvF, hv⟩ := hw
  have hwv : w - v ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change N.mkQ (w - v) = 0
    rw [map_sub, hv, sub_self]
  obtain ⟨z, hzF, hz⟩ := hDense.exists_dist_lt (⟨w - v, hwv⟩ : N) hε
  refine ⟨v + z, F.add_mem hvF hzF, ?_, ?_⟩
  · rw [map_add, hv, show N.mkQ (z : E) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr z.property, add_zero]
  · change dist (w - v) (z : E) < ε at hz
    rw [dist_comm, dist_eq_norm] at hz
    have eq : (z : E) - (w - v) = v + (z : E) - w := by abel
    simpa only [eq] using hz

/-- Density of the kernel slice gives near-minimal representatives in the
prescribed subspace, without changing their quotient values. -/
theorem quotient_representative_in_submodule (N F : Submodule ℂ E) [IsClosed (N : Set E)]
    (hDense : Dense {v : N | (v : E) ∈ F})
    {x : E ⧸ N} (hx : x ∈ N.mkQ '' (F : Set E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ F, N.mkQ u = x ∧ ‖u‖ < ‖x‖ + ε := by
  obtain ⟨w, hwq, hwn⟩ := Submodule.Quotient.norm_mk_lt x (half_pos hε)
  change N.mkQ w = x at hwq
  obtain ⟨u, huF, huq, hun⟩ := quotient_approximate_in_submodule N F hDense w (hwq.symm ▸ hx)
    (half_pos hε)
  refine ⟨u, huF, huq.trans hwq, ?_⟩
  calc
    ‖u‖ = ‖w + (u - w)‖ := congrArg norm (by abel)
    _ ≤ ‖w‖ + ‖u - w‖ := norm_add_le _ _
    _ < ‖x‖ + ε := by linarith

variable [CompleteSpace E]

/-- A summable biorthogonal perturbation extends to a global automorphism
as soon as its weighted operator norm is less than one. -/
theorem biorthogonal_perturbation_equiv (u : ℕ → E) (φ : ℕ → E →L[ℂ] ℂ)
    (hbi : ∀ m n, φ m (u n) = if m = n then 1 else 0) (y : ℕ → E)
    (hs : Summable (fun n => ‖φ n‖ * ‖y n‖))
    (hsmall : ∑' n, ‖φ n‖ * ‖y n‖ < 1) :
    ∃ T : E ≃L[ℂ] E, ∀ n, T (u n) = u n + y n := by
  let S (n : ℕ) := (φ n).smulRight (y n)
  have hsn : Summable (fun n => ‖S n‖) := by
    simpa only [S, ContinuousLinearMap.norm_smulRight_apply] using hs
  let A := ∑' n, S n
  have ha : ‖A‖ < 1 := (norm_tsum_le_tsum_norm hsn).trans_lt (by
    simpa only [S, ContinuousLinearMap.norm_smulRight_apply] using hsmall)
  have hneg : ‖-A‖ < 1 := by simpa using ha
  let T := ContinuousLinearEquiv.ofUnit (Units.oneSub (-A) hneg)
  refine ⟨T, fun n => ?_⟩
  have hT : (T : E →L[ℂ] E) = 1 + A := by
    change (↑(Units.oneSub (-A) hneg) : E →L[ℂ] E) = _
    rw [Units.val_oneSub, sub_neg_eq_add]
  have hAx : A (u n) = y n := by
    have h := (ContinuousLinearMap.apply ℂ E (u n)).hasSum hsn.of_norm.hasSum
    change HasSum (fun m => S m (u n)) (A (u n)) at h
    rw [← h.tsum_eq, tsum_eq_single n]
    · simp [S, hbi]
    · intro m hm
      simp [S, hbi, hm]
  change (T : E →L[ℂ] E) (u n) = _
  rw [hT]
  exact congrArg (u n + ·) hAx

private abbrev closedSpan (u : ℕ → E) : Submodule ℂ E :=
  (Submodule.span ℂ (range u)).topologicalClosure

private def intoClosedSpan (u : ℕ → E) (n : ℕ) : closedSpan u :=
  ⟨u n, subset_closure (Submodule.subset_span (mem_range_self n))⟩

omit [CompleteSpace E] in
private theorem intoClosedSpan_dense (u : ℕ → E) :
    Dense (Submodule.span ℂ (range (intoClosedSpan u)) : Set (closedSpan u)) := by
  let p := Submodule.span ℂ (range (intoClosedSpan u))
  let q := Submodule.span ℂ (range u)
  have hmap : p.map (closedSpan u).subtype = q := by
    rw [Submodule.map_span]
    congr 1
    rw [← range_comp]
    rfl
  intro x
  change x ∈ closure (p : Set (closedSpan u))
  rw [closure_subtype]
  change (x : E) ∈ closure (Subtype.val '' (p : Set (closedSpan u)))
  exact (congrArg (fun S : Submodule ℂ E =>
    (x : E) ∈ closure (S : Set E)) hmap).mpr x.property

omit [CompleteSpace E] in
theorem unique_closedSpan_equiv_of_automorphism (u z : ℕ → E) (T : E ≃L[ℂ] E)
    (h : ∀ n, T (u n) = z n) :
    ∃! S : closedSpan u ≃L[ℂ] closedSpan z, ∀ n, S (intoClosedSpan u n) = intoClosedSpan z n := by
  have hspan : (Submodule.span ℂ (range u)).map T.toLinearEquiv.toLinearMap =
      Submodule.span ℂ (range z) := by
    rw [Submodule.map_span]
    congr 1
    rw [← range_comp, show T.toLinearEquiv.toLinearMap ∘ u = z from funext h]
  have hcl : (closedSpan u).map T.toLinearEquiv.toLinearMap = closedSpan z := by
    apply SetLike.coe_injective
    change T '' closure (Submodule.span ℂ (range u) : Set E) =
      closure (Submodule.span ℂ (range z) : Set E)
    change T.toHomeomorph '' _ = _
    rw [T.toHomeomorph.image_closure]
    congr 1
    exact congrArg (fun S : Submodule ℂ E => (S : Set E)) hspan
  let S := T.ofSubmodules (closedSpan u) (closedSpan z) hcl
  refine ⟨S, fun n => Subtype.ext (h n), fun J hJ => ?_⟩
  have he : J.toContinuousLinearMap = S.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on (intoClosedSpan_dense u)
    rintro _ ⟨n, rfl⟩
    exact (hJ n).trans (Subtype.ext (h n)).symm
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun he x)

omit [CompleteSpace E] in
private theorem exists_perturbation_radii (ψ : ℕ → E →L[ℂ] ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n ∧ δ n ≤ ε) ∧
      ∀ y : ℕ → E, (∀ n, ‖y n‖ < δ n) →
        Summable (fun n => ‖ψ n‖ * ‖y n‖) ∧ (∑' n, ‖ψ n‖ * ‖y n‖) < 1 := by
  let weights (n : ℕ) : ℝ := (1/4) * (1/2)^n
  let δ (n : ℕ) := min ε (weights n / (‖ψ n‖ + 1))
  have hδ (n : ℕ) : 0 < δ n := lt_min hε (div_pos (by dsimp [weights]; positivity) (by positivity))
  refine ⟨δ, fun n => ⟨hδ n, min_le_left _ _⟩, fun y hy => ?_⟩
  have hbound (n : ℕ) : ‖ψ n‖ * ‖y n‖ ≤ weights n := by
    have h := (hy n).le.trans (min_le_right ε (weights n / (‖ψ n‖ + 1)))
    calc
      _ ≤ (‖ψ n‖ + 1) * ‖y n‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ weights n := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp h
  have hw : Summable weights := (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs := hw.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
  have hwSum : ∑' n, weights n = 1/2 := by
    simp only [weights, tsum_mul_left, tsum_geometric_two]
    norm_num
  exact ⟨hs, (hs.tsum_le_tsum hbound hw).trans_lt (hwSum ▸ by norm_num)⟩

/-- Corrected Lemma 10.4.2.5. Every bounded biorthogonal quotient family
bounded away from zero has controlled lifts in the prescribed subspace.
Small kernel perturbations preserve the collar and biorthogonality, and
give a unique isomorphism of the two closed spans. -/
theorem quotient_bounded_basis_lifts (N F : Submodule ℂ E) [IsClosed (N : Set E)]
    (hDense : Dense {v : N | (v : E) ∈ F})
    (x : ℕ → E ⧸ N) (φ : ℕ → (E ⧸ N) →L[ℂ] ℂ)
    (hbi : ∀ m n, φ m (x n) = if m = n then 1 else 0)
    (hx : ∀ n, x n ∈ N.mkQ '' (F : Set E))
    {r r' ε : ℝ} (hε : 0 < ε) (hεr : ε < r)
    (hnorm : ∀ n, r ≤ ‖x n‖ ∧ ‖x n‖ ≤ r') :
    ∃ (u : ℕ → E) (δ : ℕ → ℝ),
      0 < r - ε ∧
      (∀ n, u n ∈ F ∧ N.mkQ (u n) = x n ∧ r - ε ≤ ‖u n‖ ∧ ‖u n‖ ≤ r' + ε) ∧
      (∀ m n, φ m (N.mkQ (u n)) = if m = n then 1 else 0) ∧
      (∀ n, 0 < δ n) ∧
      ∀ y : ℕ → E, (∀ n, y n ∈ F ∧ y n ∈ N ∧ ‖y n‖ < δ n) →
        let z := fun n => u n + y n
        (∀ n, z n ∈ F ∧ N.mkQ (z n) = x n ∧ r - ε ≤ ‖z n‖ ∧ ‖z n‖ ≤ r' + ε) ∧
        (∀ m n, φ m (N.mkQ (z n)) = if m = n then 1 else 0) ∧
        ∃! T : closedSpan u ≃L[ℂ] closedSpan z,
          ∀ n, T (intoClosedSpan u n) = intoClosedSpan z n := by
  choose u hF hquot hu using
    fun n => quotient_representative_in_submodule N F hDense (hx n) (half_pos hε)
  let ψ (n : ℕ) : E →L[ℂ] ℂ := (φ n).comp N.mkQL
  obtain ⟨δ, hδ, hperturb⟩ := exists_perturbation_radii ψ (half_pos hε)
  have hψ (m n : ℕ) : ψ m (u n) = if m = n then 1 else 0 := by
    change φ m (N.mkQ (u n)) = _
    rw [hquot]
    exact hbi m n
  refine ⟨u, δ, sub_pos.mpr hεr, ?_, fun m n => (congrArg (φ m) (hquot n)).trans (hbi m n), fun n => (hδ n).1, ?_⟩
  · intro n
    have hl := Submodule.Quotient.norm_mk_le N (u n)
    change ‖N.mkQ (u n)‖ ≤ ‖u n‖ at hl
    rw [hquot] at hl
    exact ⟨hF n, hquot n, by linarith [hl, (hnorm n).1], by linarith [hu n, (hnorm n).2]⟩
  intro y hy z
  have hzq (n : ℕ) : N.mkQ (z n) = x n := by
    change N.mkQ (u n + y n) = x n
    rw [map_add, hquot, show N.mkQ (y n) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (hy n).2.1, add_zero]
  obtain ⟨hs, hsum⟩ := hperturb y (fun n => (hy n).2.2)
  obtain ⟨T, hT⟩ := biorthogonal_perturbation_equiv u ψ hψ y hs hsum
  refine ⟨?_, fun m n => (congrArg (φ m) (hzq n)).trans (hbi m n),
    unique_closedSpan_equiv_of_automorphism u z T hT⟩
  intro n
  have hl := Submodule.Quotient.norm_mk_le N (z n)
  change ‖N.mkQ (z n)‖ ≤ ‖z n‖ at hl
  rw [hzq] at hl
  have ht : ‖z n‖ ≤ ‖u n‖ + ‖y n‖ := norm_add_le _ _
  exact ⟨F.add_mem (hF n) (hy n).1, hzq n, by linarith [hl, (hnorm n).1],
    by linarith [ht, hu n, (hnorm n).2, (hy n).2.2, (hδ n).2]⟩

omit [CompleteSpace E] in
/-- When the initial lift has Schauder expansions, the verified perturbation
preserves those expansions with the same quotient-coordinate functionals. -/
theorem quotientSchauder_expansion_under_perturbation (N : Submodule ℂ E)
    [IsClosed (N : Set E)]
    (u z : ℕ → E) (φ : ℕ → (E ⧸ N) →L[ℂ] ℂ)
    (hquot : ∀ n, N.mkQ (u n) = N.mkQ (z n))
    (T : closedSpan u ≃L[ℂ] closedSpan z)
    (hT : ∀ n, T (intoClosedSpan u n) = intoClosedSpan z n)
    (hu : ∀ x : closedSpan u, HasSum (fun n => φ n (N.mkQ (x : E)) • intoClosedSpan u n) x)
    (x : closedSpan z) :
    HasSum (fun n => φ n (N.mkQ (x : E)) • intoClosedSpan z n) x := by
  let a := N.mkQL.comp (closedSpan u).subtypeL
  let b := N.mkQL.comp ((closedSpan z).subtypeL.comp T.toContinuousLinearMap)
  have hab : a = b := by
    apply ContinuousLinearMap.ext_on (intoClosedSpan_dense u)
    rintro _ ⟨n, rfl⟩
    change N.mkQ (u n) = N.mkQ ((T (intoClosedSpan u n) : closedSpan z) : E)
    rw [hT]
    exact hquot n
  have hq (v : closedSpan u) : N.mkQ (v : E) = N.mkQ (T v : E) :=
    DFunLike.congr_fun hab v
  have h := T.toContinuousLinearMap.hasSum (hu (T.symm x))
  simpa only [ContinuousLinearEquiv.coe_coe, map_smul, hT, hq (T.symm x),
    ContinuousLinearEquiv.apply_symm_apply] using h

/-- An isometric quotient section, as supplied by the orthogonal complement
in the Hilbert case, gives Schauder lifts in the prescribed dense subspace. -/
theorem quotient_schauder_lift_of_isometric_section (N F : Submodule ℂ E)
    [IsClosed (N : Set E)] (hDense : Dense {v : N | (v : E) ∈ F})
    (j : (E ⧸ N) →ₗᵢ[ℂ] E) (hj : ∀ x, N.mkQ (j x) = x)
    (x : ℕ → E ⧸ N) (φ : ℕ → (E ⧸ N) →L[ℂ] ℂ)
    (hbi : ∀ m n, φ m (x n) = if m = n then 1 else 0)
    (hx : ∀ n, x n ∈ N.mkQ '' (F : Set E))
    (hspan : Dense (Submodule.span ℂ (range x) : Set (E ⧸ N)))
    (hsum : ∀ a : E ⧸ N, HasSum (fun n => φ n a • x n) a) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ → E, (∀ n, u n ∈ F ∧ N.mkQ (u n) = x n ∧ ‖u n‖ < ‖x n‖ + ε) ∧
      ∀ w : closedSpan u,
        HasSum (fun n => φ n (N.mkQ (w : E)) • intoClosedSpan u n) w := by
  let ψ (n : ℕ) : E →L[ℂ] ℂ := (φ n).comp N.mkQL
  obtain ⟨δ, hδ, hperturb⟩ := exists_perturbation_radii ψ hε
  choose u huF huq hun using fun n => quotient_approximate_in_submodule N F hDense
    (j (x n)) ((hj (x n)).symm ▸ hx n) (hδ n).1
  let y (n : ℕ) := u n - j (x n)
  obtain ⟨hS, hSlt⟩ := hperturb y hun
  have hψ (m n : ℕ) : ψ m (j (x n)) = if m = n then 1 else 0 := by
    change φ m (N.mkQ (j (x n))) = _
    simpa only [hj] using hbi m n
  obtain ⟨T, hT⟩ := biorthogonal_perturbation_equiv (fun n => j (x n)) ψ hψ y hS hSlt
  let L := T.toContinuousLinearMap.comp j.toContinuousLinearMap
  have hL (n : ℕ) : L (x n) = u n := by
    change T (j (x n)) = u n
    rw [hT]
    dsimp [y]
    abel
  have hu (n : ℕ) : N.mkQ (u n) = x n := (huq n).trans (hj _)
  have hRight : N.mkQL.comp L = ContinuousLinearMap.id ℂ (E ⧸ N) := by
    apply ContinuousLinearMap.ext_on hspan
    rintro _ ⟨n, rfl⟩
    change N.mkQ (L (x n)) = x n
    simpa only [hL] using hu n
  have hQ (a : E ⧸ N) : N.mkQ (L a) = a := DFunLike.congr_fun hRight a
  have hClosed : IsClosed (range L) := by
    have he : range L = {w | L (N.mkQL w) = w} := by
      ext w
      constructor
      · rintro ⟨a, rfl⟩
        change L (N.mkQ (L a)) = L a
        rw [hQ]
      · intro hw
        exact ⟨N.mkQL w, hw⟩
    rw [he]
    exact isClosed_eq (L.continuous.comp N.mkQL.continuous) continuous_id
  have hspanL : (Submodule.span ℂ (range x)).map L.toLinearMap = Submodule.span ℂ (range u) := by
    rw [Submodule.map_span]
    congr 1
    rw [← range_comp]
    exact congrArg range (funext hL)
  have hLR (a : E ⧸ N) : L a ∈ closedSpan u := by
    have hmaps := image_closure_subset_closure_image (s := (Submodule.span ℂ (range x) : Set (E ⧸ N))) L.continuous
    have hh := hmaps (mem_image_of_mem L (hspan a))
    change L a ∈ closure (L '' (Submodule.span ℂ (range x) : Set (E ⧸ N))) at hh
    have he : L '' (Submodule.span ℂ (range x) : Set (E ⧸ N)) =
        (Submodule.span ℂ (range u) : Set E) :=
      congrArg (fun S : Submodule ℂ E => (S : Set E)) hspanL
    rw [he] at hh
    exact hh
  have hrange : (closedSpan u : Set E) ⊆ range L := by
    apply closure_minimal _ hClosed
    change (Submodule.span ℂ (range u) : Set E) ⊆ (LinearMap.range L.toLinearMap : Set E)
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact ⟨x n, hL n⟩
  let K := L.codRestrict (closedSpan u) hLR
  refine ⟨u, fun n => ⟨huF n, hu n, ?_⟩, fun w => ?_⟩
  · have ht : ‖u n‖ ≤ ‖j (x n)‖ + ‖j (x n) - u n‖ := norm_le_norm_add_norm_sub _ _
    rw [j.norm_map, norm_sub_rev] at ht
    linarith [hun n, (hδ n).2]
  · obtain ⟨a, ha⟩ := hrange w.property
    have hw : K a = w := Subtype.ext ha
    have he : N.mkQ (w : E) = a := ha ▸ hQ a
    have hval (n : ℕ) : K (x n) = intoClosedSpan u n := Subtype.ext (hL n)
    simpa only [he, map_smul, hval, hw] using K.hasSum (hsum a)

/-- The Hilbert quotient has a norm-preserving linear section into the
orthogonal complement of the closed kernel. -/
theorem hilbert_quotient_isometric_section
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Submodule ℂ H) [IsClosed (N : Set H)] :
    ∃ j : (H ⧸ N) →ₗᵢ[ℂ] H, ∀ x, N.mkQ (j x) = x := by
  let e := N.quotientEquivOrthogonal
  let j := N.orthogonal.subtypeₗᵢ.comp e.toLinearIsometry
  refine ⟨j, fun x => ?_⟩
  exact (N.quotientEquivOrthogonal_symm_eq_mk (e x).val (e x).property).symm.trans
    (e.symm_apply_apply x)

open scoped InnerProductSpace in
/-- Lemma 10.4.1.2. The quotient by the closed geometric subspace has the
actual quotient norm and is linearly isometric to its orthogonal complement.
The spectral projection chooses the unique orthogonal representative. -/
theorem hilbert_quotient_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Submodule ℂ H) [IsClosed (N : Set H)] :
    let q := N.mkQL
    let Pgeom := N.starProjection
    let Pspec := Nᗮ.starProjection
    q = q.comp Pspec ∧ q.comp Pgeom = 0 ∧
      ∃ S : (H ⧸ N) ≃ₗᵢ[ℂ] ↥Nᗮ,
        (∀ a, q (S a : H) = a) ∧
        (∀ x : H, (S (q x) : H) = Pspec x) ∧
        ∀ a, ∃! x : H, x ∈ Nᗮ ∧ q x = a := by
  dsimp only
  have hg (x : H) : N.mkQL (N.starProjection x) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (N.starProjection_apply_mem x)
  have hs (x : H) : N.mkQL (Nᗮ.starProjection x) = N.mkQL x := by
    rw [Submodule.starProjection_orthogonal_val, map_sub, hg, sub_zero]
  let S := N.quotientEquivOrthogonal
  have hS (a : H ⧸ N) : N.mkQL (S a : H) = a :=
    (N.quotientEquivOrthogonal_symm_eq_mk (S a).val (S a).property).symm.trans
      (S.symm_apply_apply a)
  have hrep (x : H) (hx : x ∈ Nᗮ) : S (N.mkQL x) = ⟨x, hx⟩ :=
    N.quotientEquivOrthogonal_mk x hx
  refine ⟨ContinuousLinearMap.ext fun x => (hs x).symm,
    ContinuousLinearMap.ext hg, S, hS, ?_, ?_⟩
  · intro x
    rw [← hs x, hrep _ (Nᗮ.starProjection_apply_mem x)]
  · intro a
    refine ⟨(S a : H), ⟨(S a).property, hS a⟩, fun x hx => ?_⟩
    exact congrArg Subtype.val ((hrep x hx.1).symm.trans (congrArg S hx.2))

end

end Masullo
