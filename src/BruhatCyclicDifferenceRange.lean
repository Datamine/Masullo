import BruhatCyclicOrbitSums
import ElementaryCyclicTails
import ElementaryRadialSchwartz
import BruhatWholeQuotientStages
import BruhatStageEvaluation

open Function Set

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- On a whole-group stage, the forward tail of a test with zero orbit sum
belongs to that same elementary stage. -/
theorem exists_wholeBruhatStage_cyclicForwardSum
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (γ : G) (hγ : 0 < (m γ).toAdd)
    (P : WholeBruhatStage G) (f : P.val.Space)
    (hzero : ∀ x : G, bruhatSchwartz_cyclicOrbitSum m γ hγ x (P.val.inclusion f) = 0) :
    ∃ v : P.val.Space, ∀ x : G, P.val.realize v x =
      bruhatSchwartz_cyclicForwardSum m γ hγ x (P.val.inclusion f) := by
  let A := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor
  let l := P.logCoordinate m
  let φ := P.coordinates
  let s : A := (φ γ).toAdd
  have hl := P.logCoordinate_isProperMap m hm
  have hs : 0 < l s := (P.logCoordinate_coordinates m γ).symm ▸ hγ
  have hcoord (x : G) (n : ℤ) : (φ (γ ^ n * x)).toAdd = (φ x).toAdd + n • s := by
    calc
      _ = (φ (γ ^ n) * φ x).toAdd := congrArg Multiplicative.toAdd (φ.map_mul _ _)
      _ = (φ γ ^ n * φ x).toAdd :=
        congrArg (fun y ↦ (y * φ x).toAdd) (φ.map_zpow γ n)
      _ = n • s + (φ x).toAdd := rfl
      _ = _ := add_comm _ _
  have hval (x : G) (n : ℤ) : f.val ((φ x).toAdd + n • s) = P.val.realize f (γ ^ n * x) :=
    (congrArg f.val (hcoord x n).symm).trans (P.realize_eq_coordinates f (γ ^ n * x)).symm
  have hzeroE (y : A) : (∑' n : ℤ, f.val (y + n • s)) = 0 := by
    obtain ⟨x, hx⟩ := P.coordinates_surjective (Multiplicative.ofAdd y)
    have hxy : (φ x).toAdd = y := congrArg Multiplicative.toAdd hx
    calc
      _ = ∑' n : ℤ, f.val ((φ x).toAdd + n • s) :=
        tsum_congr fun n ↦ congrArg (fun t ↦ f.val (t + n • s)) hxy.symm
      _ = ∑' n : ℤ, P.val.realize f (γ ^ n * x) := tsum_congr (hval x)
      _ = 0 := (bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x (P.val.inclusion f)).symm.trans (hzero x)
  let v (y : A) := ∑' n : ℕ, f.val (y + (n : ℤ) • s)
  have hv : v ∈ elementarySchwartzSubmodule P.val.2.realDim P.val.2.torusDim
      P.val.2.latticeRank P.val.2.finiteFactor := by
    apply elementarySchwartz_mem_of_log_derivative_bounds l hl
    · intro a b
      exact (elementaryCyclicSeries_smooth (fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective l
        hl.continuous s hs f a b).1
    · intro N k
      obtain ⟨D, _, hD⟩ := elementaryCyclicTail_log_decay l hl.continuous s hs N k
      exact ⟨D f, hD f hzeroE⟩
  refine ⟨⟨v, hv⟩, fun x ↦ ?_⟩
  exact (P.realize_eq_coordinates ⟨v, hv⟩ x).trans
    ((tsum_congr fun n : ℕ ↦ (hval x (n : ℤ)).trans
      (congrArg (fun g ↦ P.val.realize f (g * x)) (zpow_natCast γ n))).trans
        (bruhatSchwartz_cyclicForwardSum_apply m γ hγ x (P.val.inclusion f)).symm)

/-- An input with zero ordinary periodization has a Schwartz–Bruhat
preimage given by its forward tail on a single elementary quotient. -/
theorem bruhatSchwartzDifference_eq_of_orbitSum_zero
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : G) (hγ : 0 < (m γ).toAdd) (f : BruhatSchwartz G)
    (hzero : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0) :
    ∃ v : BruhatSchwartz G, bruhatSchwartzDifference γ v = f ∧
      ∀ x, v.val x = ∑' n : ℕ, f.val (γ ^ n * x) := by
  obtain ⟨p, u, hu⟩ := f.property
  obtain ⟨Q, hpQ⟩ := exists_wholeBruhatStage_refinement m hm hms p
  let z := p.transition Q.val hpQ u
  have hz : Q.val.inclusion z = f :=
    (p.inclusion_transition Q.val hpQ u).trans (Subtype.ext hu)
  have hz₀ (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x (Q.val.inclusion z) = 0 :=
    (congrArg (bruhatSchwartz_cyclicOrbitSum m γ hγ x) hz).trans (hzero x)
  obtain ⟨vE, hvE⟩ := exists_wholeBruhatStage_cyclicForwardSum m hm γ hγ Q z hz₀
  let v := Q.val.inclusion vE
  have hv (x : G) : v.val x = ∑' n : ℕ, f.val (γ ^ n * x) :=
    (hvE x).trans ((congrArg (bruhatSchwartz_cyclicForwardSum m γ hγ x) hz).trans
      (bruhatSchwartz_cyclicForwardSum_apply m γ hγ x f))
  have hvf (x : G) : (bruhatSchwartzDifference γ v).val x = f.val x := by
    rw [bruhatSchwartzDifference_apply, hv, hv]
    exact (bruhatSchwartz_cyclicDifference_two_tails m γ hγ f hzero).2 x
  exact ⟨v, Subtype.ext (funext hvf), hv⟩

/-- The full ordinary Schwartz–Bruhat difference range is the common kernel
of cyclic orbit sums. -/
theorem bruhatSchwartzDifference_range_eq_commonKernel
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : G) (hγ : 0 < (m γ).toAdd) :
    ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) =
      ⋂ x : G, ((bruhatSchwartz_cyclicOrbitSum m γ hγ x).ker : Set (BruhatSchwartz G)) := by
  refine subset_antisymm (subset_closure.trans
    (closure_bruhatSchwartzDifference_range_subset_commonKernel m γ hγ)) ?_
  intro f hf
  have hzero (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0 := mem_iInter.mp hf x
  obtain ⟨v, hv, _⟩ := bruhatSchwartzDifference_eq_of_orbitSum_zero m hm hms γ hγ f hzero
  exact ⟨v, hv⟩

/-- On each character isotype the ordinary periodization kernel consists of
differences of tests in that same isotype. -/
theorem bruhatSchwartzDifference_eq_of_isotypic_orbitSum_zero
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : G) (hγ : 0 < (m γ).toAdd) (f : BruhatSchwartz G)
    (hzero : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0)
    {K : Subgroup G} (χ : PontryaginDual K)
    (hf : ∀ (a : K) x, f.val (a.val⁻¹ * x) = (χ a : ℂ) * f.val x) :
    ∃ v : BruhatSchwartz G, bruhatSchwartzDifference γ v = f ∧
      ∀ (a : K) x, v.val (a.val⁻¹ * x) = (χ a : ℂ) * v.val x := by
  obtain ⟨v, hv, htail⟩ := bruhatSchwartzDifference_eq_of_orbitSum_zero m hm hms γ hγ f hzero
  refine ⟨v, hv, fun a x ↦ ?_⟩
  have he (n : ℕ) : f.val (γ ^ n * (a.val⁻¹ * x)) = (χ a : ℂ) * f.val (γ ^ n * x) := by
    rw [mul_left_comm, hf]
  rw [htail, htail]
  simp_rw [he]
  rw [tsum_mul_left]

/-- The compact difference solution in Proposition 4.5.2.1(3) keeps the
subgroup invariance and belongs to the entire-decay space. The support
interval is shifted at the lower endpoint by one logarithmic period. -/
theorem bruhatCyclicInvariantCompact_difference
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : G) (hγ : 0 < (m γ).toAdd) (K : Subgroup G)
    (f : BruhatSchwartz G) (a b : ℝ)
    (hf : support f.val ⊆ (fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
    (hK : ∀ (k : K) x, f.val (k.val⁻¹ * x) = f.val x)
    (hzero : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0) :
    ∃ v : ModulatedExponentialInductive m univ,
      support v.val ⊆ (fun x ↦ (m x).toAdd) ⁻¹' Icc (a + (m γ).toAdd) b ∧
      (∀ (k : K) x, v.val (k.val⁻¹ * x) = v.val x) ∧
      ∀ x, v.val x - v.val (γ * x) = f.val x := by
  obtain ⟨v, hvS, hvC, hv⟩ := bruhatSchwartz_cyclicDifference_compact_source m hm γ hγ f a b hf hzero
  have htriv (k : K) (x : G) :
      f.val (k.val⁻¹ * x) = ((1 : PontryaginDual K) k : ℂ) * f.val x := by
    simpa using hK k x
  obtain ⟨u, hu, huK⟩ :=
    bruhatSchwartzDifference_eq_of_isotypic_orbitSum_zero m hm hms γ hγ f hzero 1 htriv
  have hinj : Injective (bruhatSchwartzDifference γ) := by
    simpa [bruhatSchwartzDifferenceProduct] using
      (bruhatSchwartzDifferenceProduct_injective m [γ] (by simpa using hγ))
  have huv : u = v := hinj (hu.trans hv.symm)
  let z : BruhatCompactTest G := BruhatCompactTest.algebraicEquiv.symm ⟨v, hvC⟩
  let w := bruhatCompactTest_toModulatedExponentialInductive m univ z
  have hw : w.val = v.val :=
    congrArg (fun x : bruhatCompactTestSubmodule (G := G) ↦ x.val.val)
      (BruhatCompactTest.algebraicEquiv.apply_symm_apply ⟨v, hvC⟩)
  refine ⟨w, hw.symm ▸ hvS, fun k x ↦ ?_, fun x ↦ ?_⟩
  · rw [hw, ← huv]
    simpa using huK k x
  · rw [hw]
    exact (bruhatSchwartzDifference_apply γ v x).symm.trans
      (congrArg (fun g : BruhatSchwartz G ↦ g.val x) hv)

/-- The range is closed in the actual final Schwartz–Bruhat topology. -/
theorem bruhatSchwartzDifference_isClosed_range
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : G) (hγ : 0 < (m γ).toAdd) :
    IsClosed ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) := by
  rw [bruhatSchwartzDifference_range_eq_commonKernel m hm hms γ hγ]
  exact isClosed_iInter fun x ↦ (bruhatSchwartz_cyclicOrbitSum m γ hγ x).isClosed_ker

/-- A continuous family of tests with zero orbit sums can be divided
continuously by the cyclic difference if it maps each source Schwartz stage
continuously into a single whole-group stage. -/
theorem exists_bruhatSchwartz_cyclicDivision
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (γ : G) (hγ : 0 < (m γ).toAdd)
    (M : BruhatSchwartz G →L[ℂ] BruhatSchwartz G)
    (hM : ∀ f x, bruhatSchwartz_cyclicOrbitSum m γ hγ x (M f) = 0)
    (hStage : ∀ p : BruhatSchwartzStage G, ∃ (Q : WholeBruhatStage G)
      (V : p.Space →L[ℂ] Q.val.Space), ∀ f, Q.val.inclusion (V f) = M (p.inclusion f)) :
    ∃ D : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
      (∀ f, bruhatSchwartzDifference γ (D f) = M f) ∧
      ∀ f x, (D f).val x = bruhatSchwartz_cyclicForwardSum m γ hγ x (M f) := by
  let A (x : G) := (bruhatSchwartz_cyclicForwardSum m γ hγ x).comp M
  have hDescent (p : BruhatSchwartzStage G) :
      ∃ (q : BruhatSchwartzStage G) (L : p.Space →L[ℂ] q.Space),
        ∀ f x, q.realize (L f) x = A x (p.inclusion f) := by
    obtain ⟨Q, V, hV⟩ := hStage p
    have hval (f : p.Space) : ∃ u : Q.val.Space, ∀ x, Q.val.realize u x = A x (p.inclusion f) := by
      have hz (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x (Q.val.inclusion (V f)) = 0 :=
        (congrArg (bruhatSchwartz_cyclicOrbitSum m γ hγ x) (hV f)).trans (hM _ x)
      obtain ⟨u, hu⟩ := exists_wholeBruhatStage_cyclicForwardSum m hm γ hγ Q (V f) hz
      exact ⟨u, fun x ↦ (hu x).trans (congrArg (bruhatSchwartz_cyclicForwardSum m γ hγ x) (hV f))⟩
    exact ⟨Q.val, bruhatStage_exists_clm_of_evaluation p Q.val id surjective_id
      (fun x ↦ (A x).comp p.inclusionCLM) hval⟩
  obtain ⟨D, hD⟩ := bruhatSchwartz_exists_clm_of_stage_evaluation id surjective_id A hDescent
  refine ⟨D, fun f ↦ Subtype.ext (funext fun x ↦ ?_), hD⟩
  have hEval (z : G) : (D f).val z = ∑' n : ℕ, (M f).val (γ ^ n * z) :=
    (hD f z).trans (bruhatSchwartz_cyclicForwardSum_apply m γ hγ z (M f))
  exact (bruhatSchwartzDifference_apply γ (D f) x).trans
    ((congrArg₂ (· - ·) (hEval x) (hEval (γ * x))).trans
      ((bruhatSchwartz_cyclicDifference_two_tails m γ hγ (M f) (hM f)).2 x))

end

end Masullo
