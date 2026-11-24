import SLocalArchSchwartzDilation
import SchwartzComplete
import FrechetFactorization

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev L (v : S) := v.val.adicCompletion F
private abbrev K := SLocalThetaNormOne F S
private abbrev FiniteTests := locallyConstantTests (∀ v : S, L F S v)

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private def sliceCoeff (ω : PontryaginDual (K F S)) (ψ : FiniteTests F S) (w : ℂ) (k : ℕ) :
    Arch F →ₗ[ℂ] ℂ :=
  (sLocalLaurentCoeff F S μ ω w k).toLinearMap.comp ((sLocalBruhatPure F S).flip ψ)

/-- All coefficients through a prescribed order at one pole can be
corrected together in the fixed Schwartz slice, with no negative
Laurent coefficients at the other selected centers. -/
theorem exists_sLocalArchFixedFiniteBlockCorrection (ω : PontryaginDual (K F S)) :
    ∃ g : ∀ v : S, locallyConstantTests (L F S v), (∀ v, (g v).val 0 = 0) ∧
      let ψ := locallyConstantTestPiProduct g
      ∀ (T : Finset ℂ) (c : ℂ) (k : ℕ), k ≤ sLocalArchPoleCount F S ω c →
        ∀ (b : ℕ → ℂ) (Q : Finset (ℕ × ℕ)), (∀ i ∈ Q, c.re + (i.2 : ℝ) / Module.finrank ℚ F < 0) →
        ∀ ε : ℝ, 0 < ε → ∃ f : Arch F,
          (∀ i ∈ Q, SchwartzMap.seminorm ℂ i.1 i.2 f < ε) ∧
          (∀ j, 0 < j → j ≤ k →
            sLocalLaurentCoeff F S μ ω c j (sLocalBruhatPure F S f ψ) = b j) ∧
          (∀ j > k, sLocalLaurentCoeff F S μ ω c j (sLocalBruhatPure F S f ψ) = 0) ∧
          ∀ w ∈ T, w ≠ c → ∀ j > 0,
            sLocalLaurentCoeff F S μ ω w j (sLocalBruhatPure F S f ψ) = 0 := by
  obtain ⟨g, h0, hg⟩ := exists_sLocalArchFixedFiniteIsolatedCorrection F S μ ω
  refine ⟨g, h0, ?_⟩
  let ψ := locallyConstantTestPiProduct g
  change ∀ (T : Finset ℂ) (c : ℂ) (k : ℕ), _
  let B := sliceCoeff F S μ ω ψ
  intro T c k
  induction k with
  | zero =>
    intro _ b Q hQ ε hε
    refine ⟨0, ?_, fun j hj hle ↦ (not_lt_of_ge hle hj).elim, ?_, ?_⟩
    · intro i hi
      simpa only [map_zero] using hε
    · intro j hj
      exact (B c j).map_zero
    · intro w hw hne j hj
      exact (B w j).map_zero
  | succ k ih =>
    intro hle b Q hQ ε hε
    obtain ⟨u, hu, huv, huh, hur⟩ :=
      hg T c (k+1) (Nat.succ_pos _) hle (b (k+1)) Q hQ (ε/2) (by positivity)
    obtain ⟨v, hv, hvv, hvh, hvr⟩ := ih ((Nat.le_succ k).trans hle)
      (fun j ↦ b j - B c j u) Q hQ (ε/2) (by positivity)
    refine ⟨u+v, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact (map_add_le_add (SchwartzMap.seminorm ℂ i.1 i.2) u v).trans_lt
        (by linarith [hu i hi, hv i hi])
    · intro j hj hjle
      change B c j (u+v) = b j
      rw [map_add]
      by_cases hjk : j ≤ k
      · have he : B c j v = b j - B c j u := hvv j hj hjk
        rw [he]
        ring
      · have he : j = k+1 := by omega
        subst j
        have hu' : B c (k+1) u = b (k+1) := huv
        have hv' : B c (k+1) v = 0 := hvh (k+1) (Nat.lt_succ_self _)
        rw [hu', hv', add_zero]
    · intro j hj
      change B c j (u+v) = 0
      rw [map_add, show B c j u = 0 from huh j hj,
        show B c j v = 0 from hvh j ((Nat.lt_succ_self k).trans hj), add_zero]
    · intro w hw hne j hj
      change B w j (u+v) = 0
      rw [map_add, show B w j u = 0 from hur w hw hne j hj,
        show B w j v = 0 from hvr w hw hne j hj, add_zero]

omit [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ]
  [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem slice_continuous (ψ : FiniteTests F S) :
    Continuous (fun φ : Arch F ↦ sLocalBruhatPure F S φ ψ) := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  letI : IsTopologicalAddGroup (FiniteTests F S) := (finest_withSeminorms _).topologicalAddGroup
  exact ((continuous_inductiveTensor_lift_iff (sLocalBruhatPure F S)).mp
    (sLocalBruhatPure_lift_continuous F S)).1 ψ

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem sliceCoeff_continuous (ω : PontryaginDual (K F S)) (ψ : FiniteTests F S)
    (w : ℂ) (k : ℕ) : Continuous (sliceCoeff F S μ ω ψ w k) :=
  (sLocalLaurentCoeff F S μ ω w k).continuous.comp (slice_continuous F S ψ)

/-- Every full array of archimedean Laurent coefficients comes from one
Schwartz test with fixed finite factors. The corrections converge in the
original Schwartz topology. -/
theorem exists_sLocalArchFixedFiniteSimultaneousInterpolation (ω : PontryaginDual (K F S)) :
    ∃ g : ∀ v : S, locallyConstantTests (L F S v), (∀ v, (g v).val 0 = 0) ∧
      let ψ := locallyConstantTestPiProduct g
      ∀ a : SLocalArchPoleIndex F S ω → ℂ, ∃ f : Arch F,
        ∀ i : SLocalArchPoleIndex F S ω,
          sLocalLaurentCoeff F S μ ω i.val.1 i.val.2 (sLocalBruhatPure F S f ψ) = a i := by
  obtain ⟨g, h0, hg⟩ := exists_sLocalArchFixedFiniteBlockCorrection F S μ ω
  obtain ⟨e⟩ := sLocalArchPoleCenter_enumerable F S ω
  refine ⟨g, h0, fun a ↦ ?_⟩
  let ψ := locallyConstantTestPiProduct g
  let B := sliceCoeff F S μ ω ψ
  let c (n : ℕ) := (e n).val
  let M (n : ℕ) := sLocalArchPoleCount F S ω (c n)
  let T (n : ℕ) := (Finset.range n).image c
  let Q (n : ℕ) := (Finset.Iic (n, n)).filter fun i : ℕ × ℕ ↦
    (c n).re + (i.2 : ℝ) / Module.finrank ℚ F < 0
  let b (n j : ℕ) : ℂ := if h : 0 < j ∧ j ≤ M n then a ⟨(c n, j), h⟩ else 0
  let ε (n : ℕ) : ℝ := (1/2)^n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose H hS hV _ hR using fun (n : ℕ) (x : Arch F) ↦
    hg (T n) (c n) (M n) le_rfl (fun j ↦ b n j - B (c n) j x) (Q n)
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (ε n) (hε n)
  let x : ℕ → Arch F := Nat.rec 0 (fun n x ↦ x + H n x)
  let u (n : ℕ) : Arch F := H n (x n)
  have hstep (n : ℕ) : x (n + 1) = x n + u n := rfl
  have hxsum (n : ℕ) : x n = ∑ j ∈ Finset.range n, u j := by
    induction n with
    | zero => simp [x]
    | succ n ih => rw [hstep, Finset.sum_range_succ, ih]
  have hQ (i : ℕ × ℕ) : ∀ᶠ n in atTop, i ∈ Q n := by
    have hc := sLocalArchPoleCenter_re_tendsto_atBot F S ω e
    let r : ℝ := (i.2 : ℝ) / Module.finrank ℚ F
    have he : ∀ᶠ n in atTop, (c n).re ≤ -r - 1 :=
      tendsto_atBot.mp hc _
    filter_upwards [eventually_ge_atTop (max i.1 i.2), he] with n hn hn'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Iic.mpr ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩, ?_⟩
    change (c n).re + r < 0
    linarith
  have hs (k j : ℕ) : Summable (fun n ↦ SchwartzMap.seminorm ℂ k j (u n)) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hQ (k,j))
    apply (summable_nat_add_iff N).mp
    refine Summable.of_nonneg_of_le (fun n ↦ apply_nonneg _ _) (fun n ↦ ?_)
      ((summable_nat_add_iff N).mpr (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)))
    exact (hS (n+N) (x (n+N)) (k,j) (hN _ (Nat.le_add_left _ _))).le
  obtain ⟨f, hf⟩ := schwartz_tendsto_partialSums u hs
  have hlim : Tendsto x atTop (𝓝 f) := hf.congr (fun n ↦ (hxsum n).symm)
  refine ⟨f, fun i ↦ ?_⟩
  let n := e.symm ⟨i.val.1, i.property.1.trans_le i.property.2⟩
  let j := i.val.2
  have hcn : c n = i.val.1 := congrArg Subtype.val (e.apply_symm_apply _)
  have hj : 0 < j := i.property.1
  have hjM : j ≤ M n := by
    change j ≤ sLocalArchPoleCount F S ω (c n)
    rw [hcn]
    exact i.property.2
  have hb : b n j = a i := by
    dsimp only [b]
    rw [dite_eq_left ⟨hj, hjM⟩]
    congr 1
    exact Subtype.ext (Prod.ext hcn rfl)
  have hstay (m : ℕ) (hm : n+1 ≤ m) : B (c n) j (x m) = b n j := by
    refine Nat.le_induction ?_ (fun m hnm ihm ↦ ?_) m hm
    · rw [hstep, map_add, show B (c n) j (u n) = b n j - B (c n) j (x n) from hV n (x n) j hj hjM]
      ring
    · have hnmem : c n ∈ T m :=
        Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hnm, rfl⟩
      have hne : c n ≠ c m := fun h ↦
        (Nat.ne_of_lt hnm) (e.injective (Subtype.ext h))
      have hz : B (c n) j (u m) = 0 := hR m (x m) (c n) hnmem hne j hj
      rw [hstep, map_add, hz, add_zero, ihm]
  have hConst : (fun m ↦ B (c n) j (x m)) =ᶠ[atTop] fun _ ↦ b n j :=
    eventually_atTop.mpr ⟨n+1, hstay⟩
  have hVal := tendsto_nhds_unique_of_eventuallyEq
    ((sliceCoeff_continuous F S μ ω ψ (c n) j).continuousAt.tendsto.comp hlim)
    tendsto_const_nhds hConst
  change B i.val.1 j f = a i
  rw [← hcn, hVal, hb]

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

include hν in
/-- The original archimedean principal-part quotient is continuously
linearly equivalent to the product of all its Laurent coordinates. -/
def sLocalArchPolarQuotient_equiv_coefficients (ω : PontryaginDual (K F S)) :
    (sLocalArchPolarImage F S ν ω ⧸ sLocalArchPolarKernel F S μ ν hν ω) ≃L[ℂ]
      (SLocalArchPoleIndex F S ω → ℂ) := by
  let V := sLocalArchPolarImage F S ν ω
  let K₀ := sLocalArchPolarKernel F S μ ν hν ω
  let Q := sLocalArchPolarQuotientCoefficients F S μ ν hν ω
  let I := SLocalArchPoleIndex F S ω
  let e := Classical.choice (sLocalArchPoleIndex_enumerable F S ω)
  letI : Countable I := e.symm.injective.countable
  let w := exists_sLocalArchFixedFiniteSimultaneousInterpolation F S μ ω
  let g := w.choose
  have h0 := w.choose_spec.1
  have hg := w.choose_spec.2
  let ψ := locallyConstantTestPiProduct g
  let A : Arch F →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i ↦
    ⟨sliceCoeff F S μ ω ψ i.val.1 i.val.2, sliceCoeff_continuous F S μ ω ψ i.val.1 i.val.2⟩
  have hA : Function.Surjective A := fun a ↦ by
    obtain ⟨f, hf⟩ := hg a
    exact ⟨f, funext hf⟩
  letI : BaireSpace (I → ℂ) := BaireSpace.of_completelyPseudoMetrizable
  letI : @CompleteSpace (Arch F) (IsTopologicalAddGroup.rightUniformSpace (Arch F)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact completeSpace_schwartzMap
  have hAopen : IsOpenMap A := isOpenMap_of_surjective_complete_baire A hA
  let P : Arch F →L[ℂ] sLocalBruhatImage F S :=
    ⟨(sLocalBruhatPure F S).flip ψ, slice_continuous F S ψ⟩
  let M := sLocalHomogeneousThetaKernel F S ν ω
  have hP (f : Arch F) :
      M.mkQL (P f) ∈ V := ⟨P f, Submodule.subset_span ⟨f, g, fun v _ ↦ h0 v, rfl⟩, rfl⟩
  let H : Arch F →L[ℂ] (V ⧸ K₀) := K₀.mkQL.comp ((M.mkQL.comp P).codRestrict V hP)
  have heq (f : Arch F) : Q (H f) = A f := rfl
  have hQinj : Function.Injective Q := sLocalArchPolarQuotientCoefficients_injective F S μ ν hν ω
  have hQ : Function.Surjective Q := fun y ↦ by
    obtain ⟨f, hf⟩ := hA y
    exact ⟨H f, (heq f).trans hf⟩
  have hH : Function.Surjective H := fun q ↦ by
    obtain ⟨f, hf⟩ := hA (Q q)
    exact ⟨f, hQinj ((heq f).trans hf)⟩
  have hQopen : IsOpenMap Q := by
    intro U hU
    have hE : A '' (H ⁻¹' U) = Q '' U := by
      ext z
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact ⟨H f, hf, heq f⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨f, rfl⟩ := hH q
        exact ⟨f, hq, (heq f).symm⟩
    rw [← hE]
    exact hAopen _ (hU.preimage H.continuous)
  let D := LinearEquiv.ofBijective Q.toLinearMap ⟨hQinj, hQ⟩
  exact { toLinearEquiv := D
          continuous_toFun := Q.continuous
          continuous_invFun := D.toEquiv.continuous_symm_iff.mpr hQopen }

include hν in
/-- The original quotient topology is also induced by the family of
canonical finite-cutoff quotient maps. -/
theorem sLocalArchPolarToCutoff_isInducing (ω : PontryaginDual (K F S)) :
    IsInducing (fun q N ↦ sLocalArchPolarToCutoff F S μ ν hν ω N q) := by
  let V := sLocalArchPolarImage F S ν ω
  let K₀ := sLocalArchPolarKernel F S μ ν hν ω
  let I := SLocalArchPoleIndex F S ω
  let X (N : InfinitePlace F → ℕ) := V ⧸ sLocalArchPoleFiltration F S μ ν hν ω N
  let J (q : V ⧸ K₀) (N : InfinitePlace F → ℕ) : X N := sLocalArchPolarToCutoff F S μ ν hν ω N q
  let A := sLocalArchPolarQuotient_equiv_coefficients F S μ ν hν ω
  choose n hn using fun i : I ↦ (sLocalArchPoleCount_pos_iff_exists_cutoff F S ω i.val.1).mp
    (i.property.1.trans_le i.property.2)
  let N (i : I) (_ : InfinitePlace F) := n i
  let j (i : I) : SLocalArchCutoffIndex F S ω (N i) := ⟨i, hn i⟩
  let R (x : ∀ N₀, X N₀) (i : I) : ℂ :=
    sLocalArchPoleFiltration_equiv_coefficients F S μ ν hν ω (N i) (x (N i)) (j i)
  have hR : Continuous R := continuous_pi fun i ↦
    (continuous_apply (j i)).comp
      ((sLocalArchPoleFiltration_equiv_coefficients F S μ ν hν ω (N i)).continuous.comp
        (continuous_apply (N i)))
  have hEq (q : V ⧸ K₀) : R (J q) = A q := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective K₀ q
    rfl
  have hL : Function.LeftInverse (A.symm ∘ R) J := by
    intro q
    change A.symm (R (J q)) = q
    rw [hEq, A.symm_apply_apply]
  exact (hL.isEmbedding (A.symm.continuous.comp hR)
    (continuous_pi fun N₀ ↦ (sLocalArchPolarToCutoff F S μ ν hν ω N₀).continuous)).isInducing

end

end Masullo
