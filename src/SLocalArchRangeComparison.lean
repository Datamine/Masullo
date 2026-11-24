import SLocalEntireStrip
import SLocalArchSimultaneousInterpolation

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S
private abbrev L (v : S) := v.val.adicCompletion F

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

private abbrev N := sLocalFiniteNonzeroTestSubspace F S Finset.univ

include hν in
private theorem full_finiteImage_rep_of_arch_poles (ω : PontryaginDual (K F S)) (f : E F S)
    (hf : ∀ (c : ℂ) (k : ℕ), sLocalArchPoleCount F S ω c < k →
      sLocalLaurentCoeff F S μ ω c k f = 0) :
    ∃ g : N F S,
      sLocalMeromorphicZetaComponent F S μ ω g.val = sLocalMeromorphicZetaComponent F S μ ω f := by
  obtain ⟨p, hp, hinterp⟩ := exists_sLocalArchFixedFiniteSimultaneousInterpolation F S μ ω
  obtain ⟨φ, hφ⟩ := hinterp fun i ↦ sLocalLaurentCoeff F S μ ω i.val.1 i.val.2 f
  let b := sLocalBruhatPure F S φ (locallyConstantTestPiProduct p)
  have hb : b ∈ N F S := Submodule.subset_span ⟨φ, p, fun v _ ↦ hp v, rfl⟩
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let q : sLocalArchPolarImage F S ν ω := ⟨M.mkQ b, b, hb, rfl⟩
  have hbez (c : ℂ) (k : ℕ) (hk : sLocalArchPoleCount F S ω c < k) :
      sLocalLaurentCoeff F S μ ω c k b = 0 :=
    sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω hk q
  have hdiff (c : ℂ) (k : ℕ) (hk : 0 < k) :
      sLocalLaurentCoeff F S μ ω c k (f - b) = 0 := by
    rw [map_sub]
    by_cases ht : k ≤ sLocalArchPoleCount F S ω c
    · exact sub_eq_zero.mpr (hφ ⟨(c, k), hk, ht⟩).symm
    · rw [hf c k (lt_of_not_ge ht), hbez c k (lt_of_not_ge ht), sub_zero]
  have hentire : AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω (f - b)) univ) univ := by
    have hm : MeromorphicOn (Z F S μ ω (f - b)) univ :=
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ (f - b)).meromorphicOn
    intro c hc
    apply (meromorphicNFOn_toMeromorphicNFOn _ univ hc).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hc]
    simpa using (sLocalLaurentCoeff_vanish_iff F S μ ω c 0 (f - b)).mp (hdiff c)
  obtain ⟨g, hg⟩ := (sLocal_entire_iff_flat_and_profile F S μ ν hν ω (f - b)).1.mp hentire
  have hgN : g.val ∈ N F S := by
    have hle : sLocalPolarFreeTestSubspace F S ≤ N F S := by
      rw [sLocalPolarFreeTestSubspace_eq_inf]
      exact inf_le_right
    exact hle g.property
  refine ⟨⟨b + g.val, (N F S).add_mem hb hgN⟩, ?_⟩
  change sLocalMeromorphicZetaComponent F S μ ω (b + g.val) = _
  rw [map_add, ← hg, map_sub, add_comm _ (_ - _), sub_add_cancel]

include hν in
/-- The full finite principal-value image is exactly the bounded-archimedean
pole subspace of the actual homogeneous theta quotient. -/
theorem sLocal_mk_mem_full_finiteImage_iff_arch_poleBound
    (ω : PontryaginDual (K F S)) (f : E F S) :
    (sLocalHomogeneousThetaKernel F S ν ω).mkQ f ∈ sLocalArchPolarImage F S ν ω ↔
      ∀ c : ℂ, ((-(sLocalArchPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (Z F S μ ω f) c := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  constructor
  · intro hf c
    let q : sLocalArchPolarImage F S ν ω := ⟨M.mkQ f, hf⟩
    exact (sLocalLaurentCoeff_vanish_iff F S μ ω c _ f).mp fun k hk ↦
      sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω hk q
  · intro hf
    obtain ⟨g, hg⟩ := full_finiteImage_rep_of_arch_poles F S μ ν hν ω f (fun c ↦
      (sLocalLaurentCoeff_vanish_iff F S μ ω c _ f).mpr (hf c))
    refine ⟨g.val, g.property, ?_⟩
    change (Submodule.Quotient.mk (p := M) g.val) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq, mem_sLocalHomogeneousThetaKernel_iff,
      sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μ ν hν, map_sub, hg, sub_self]

include hν in
/-- The homogeneous image of the full finite principal-value operator is
closed in the original S-local homogeneous theta quotient. -/
theorem sLocalArchPolarImage_eq_arch_poleBound
    (ω : PontryaginDual (K F S)) :
    sLocalArchPolarImage F S ν ω =
      sLocalThetaPoleBound F S μ ν hν ω (sLocalArchPoleCount F S ω) := by
  apply Submodule.ext
  intro q
  obtain ⟨f, rfl⟩ := (sLocalHomogeneousThetaKernel F S ν ω).mkQ_surjective q
  exact (sLocal_mk_mem_full_finiteImage_iff_arch_poleBound F S μ ν hν ω f).trans
    (mem_sLocalThetaPoleBound_mk F S μ ν hν ω _ f).symm

include hν in
/-- Selected finite principal values give the same homogeneous range
whenever the selection contains all unramified finite places. -/
theorem sLocalFiniteNonzeroTestSubspace_map_eq_arch_poleBound
    (ω : PontryaginDual (K F S)) (T : Finset S)
    (hT : sLocalUnramifiedPlaceSelection F S ω ⊆ T) :
    (sLocalFiniteNonzeroTestSubspace F S T).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ =
      sLocalThetaPoleBound F S μ ν hν ω (sLocalArchPoleCount F S ω) := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  have hm : Antitone (sLocalFiniteNonzeroTestSubspace F S) := by
    intro A B hAB
    apply Submodule.span_mono
    rintro _ ⟨φ, g, hg, rfl⟩
    exact ⟨φ, g, fun v hv ↦ hg v (hAB hv), rfl⟩
  rw [← sLocalArchPolarImage_eq_arch_poleBound F S μ ν hν ω]
  change _ = (N F S).map M.mkQ
  refine le_antisymm ?_ (Submodule.map_mono (hm (Finset.subset_univ T)))
  rw [← (sLocalFiniteNonzeroTestSubspace_images F S μ ν hν ω).1]
  exact Submodule.map_mono (hm hT)

/-- The coefficient condition in Proposition 7.2.2.1(1) is a lower bound
on the order of the pole-cleared local transform, for any selected set. -/
theorem sLocal_removedLaurent_iff_normalized_order
    (ω : PontryaginDual (K F S)) (T : Finset S) (f : E F S) (c : ℂ) :
    (∀ k > sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c,
      sLocalLaurentCoeff F S μ ω c k f = 0) ↔
      (sLocalSelectedFinitePoleCount F S ω T c : WithTop ℤ) ≤
        meromorphicOrderAt (sLocalEulerNormalizedMellin F S μ ω f) c := by
  let d := sLocalPoleCount F S ω c
  let t := sLocalSelectedFinitePoleCount F S ω T c
  have htd : t ≤ d := sLocalSelectedFinitePoleCount_le F S ω T c
  have hD : AnalyticAt ℂ (sLocalEulerDenominator F S ω) c :=
    sLocalEulerDenominator_analytic F S ω c
  obtain ⟨U, hU, hUnz, he, _⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω c
  have hDorder : meromorphicOrderAt (sLocalEulerDenominator F S ω) c = (d : WithTop ℤ) := by
    rw [hD.meromorphicOrderAt_eq, hD.analyticOrderAt_eq_natCast.mpr ⟨U, hU, hUnz, he⟩,
      ENat.map_natCast]
    rfl
  have hOrder : meromorphicOrderAt (sLocalEulerNormalizedMellin F S μ ω f) c =
      (d : WithTop ℤ) + meromorphicOrderAt (Z F S μ ω f) c := by
    rw [meromorphicOrderAt_congr (sLocalEulerNormalizedMellin_eq_germ F S μ ω f c)]
    change meromorphicOrderAt (sLocalEulerDenominator F S ω * Z F S μ ω f) c = _
    rw [meromorphicOrderAt_mul hD.meromorphicAt
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f c), hDorder]
  rw [sLocalLaurentCoeff_vanish_iff, hOrder]
  change ((-((d - t : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ _ ↔ (t : WithTop ℤ) ≤ _
  cases h : meromorphicOrderAt (Z F S μ ω f) c with
  | top => simp
  | coe z =>
    rw [show (t : WithTop ℤ) = ((t : ℤ) : WithTop ℤ) by rfl,
      show (d : WithTop ℤ) = ((d : ℤ) : WithTop ℤ) by rfl, ← WithTop.coe_add]
    simp only [WithTop.coe_le_coe]
    omega

omit [∀ v : S, BorelSpace (L F S v)ˣ] [MeasurableSpace (InfiniteAdeleRing F)ˣ]
  [∀ v : S, MeasurableSpace (L F S v)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem selectedFinitePoleCount_add_compl
    (ω : PontryaginDual (K F S)) (T : Finset S) (c : ℂ) :
    sLocalSelectedFinitePoleCount F S ω T c +
      sLocalSelectedFinitePoleCount F S ω (Finset.univ \ T) c =
        (sLocalFinitePolesAt F S ω c).card := by
  let p (v : S) := finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) c = 0
  have hunion : T ∪ (Finset.univ \ T) = Finset.univ := by
    ext v
    by_cases hv : v ∈ T <;> simp [hv]
  have hdisj : Disjoint (T.filter p) ((Finset.univ \ T).filter p) := by
    refine Finset.disjoint_left.mpr fun v hv hw ↦ ?_
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2 (Finset.mem_filter.mp hv).1
  change (T.filter p).card + ((Finset.univ \ T).filter p).card =
    (sLocalFinitePolesAt F S ω c).card
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, hunion]
  rfl

include hν in
private theorem sLocalPrincipalValues_cancel_meromorphic_zero
    (ω : PontryaginDual (K F S)) (T : Finset S) (f : E F S)
    (h : sLocalMeromorphicZetaComponent F S μ ω (sLocalWeilPrincipalValues F S T f) = 0) :
    sLocalMeromorphicZetaComponent F S μ ω f = 0 := by
  change Submodule.Quotient.mk (p := zeroMeromorphicGerms)
    (⟨Z F S μ ω (sLocalWeilPrincipalValues F S T f),
      sLocalProductZetaContinued_meromorphic F S μ ω _ _ _⟩ : meromorphicRepresentatives) = 0 at h
  change Submodule.Quotient.mk (p := zeroMeromorphicGerms)
    (⟨Z F S μ ω f, sLocalProductZetaContinued_meromorphic F S μ ω _ _ _⟩ :
      meromorphicRepresentatives) = 0
  rw [Submodule.Quotient.mk_eq_zero] at h ⊢
  change ∀ z : ℂ, Z F S μ ω (sLocalWeilPrincipalValues F S T f) =ᶠ[𝓝[≠] z] 0 at h
  change ∀ z : ℂ, Z F S μ ω f =ᶠ[𝓝[≠] z] 0
  intro z
  filter_upwards [h z, sLocalWeilPrincipalValues_continued F S μ ν hν ω T f z,
    sLocalSelectedEulerMultiplier_eventually_ne_zero F S ω T z] with w hzero he hn
  exact (mul_eq_zero.mp (he.symm.trans hzero)).resolve_left hn

set_option maxHeartbeats 600000 in
include hν in
/-- The two local conditions in Proposition 7.2.2.1 are equivalent for
every selected set of finite places. The complementary product reduces
the range assertion to the full finite range, and its multiplier cancels. -/
theorem sLocal_mk_mem_selected_finiteImage_iff_poleBound
    (ω : PontryaginDual (K F S)) (T : Finset S) (f : E F S) :
    (sLocalHomogeneousThetaKernel F S ν ω).mkQ f ∈
      (sLocalFiniteNonzeroTestSubspace F S T).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ ↔
      ∀ c : ℂ,
        ((sLocalSelectedFinitePoleCount F S ω T c : ℤ) - (sLocalPoleCount F S ω c : ℤ) : ℤ) ≤
          meromorphicOrderAt (Z F S μ ω f) c := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let Zc := sLocalMeromorphicZetaComponent F S μ ω
  constructor
  · rintro ⟨g, hg, he⟩ c
    rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace] at hg
    obtain ⟨g, rfl⟩ := hg
    have hbound := sLocalWeilPrincipalValues_pole_le F S μ ν hν ω T g c
    have hcoeff := (sLocalLaurentCoeff_vanish_iff F S μ ω c
      (sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c)
      (sLocalWeilPrincipalValues F S T g)).mpr ?_
    · have hh : ∀ k > sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c,
          sLocalLaurentCoeff F S μ ω c k f = 0 := by
        intro k hk
        change sLocalThetaLaurentCoeff F S μ ν hν ω c k (M.mkQ f) = 0
        rw [← he]
        exact hcoeff k hk
      have heq := (sLocalLaurentCoeff_vanish_iff F S μ ω c _ f).mp hh
      rw [Nat.cast_sub (sLocalSelectedFinitePoleCount_le F S ω T c), neg_sub] at heq
      exact heq
    · rw [Nat.cast_sub (sLocalSelectedFinitePoleCount_le F S ω T c), neg_sub]
      exact hbound
  · intro hf
    let U := Finset.univ \ T
    let P := sLocalWeilPrincipalValues F S U
    have hArch : ∀ c : ℂ, ((-(sLocalArchPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (Z F S μ ω (P f)) c := by
      intro c
      rw [show P = sLocalWeilPrincipalValues F S U from rfl,
        sLocalWeilPrincipalValues_order F S μ ν hν ω U f c]
      have h := hf c
      have ha := add_le_add_right h (sLocalSelectedFinitePoleCount F S ω U c : WithTop ℤ)
      rw [show (sLocalSelectedFinitePoleCount F S ω U c : WithTop ℤ) =
        ((sLocalSelectedFinitePoleCount F S ω U c : ℤ) : WithTop ℤ) from rfl,
        ← WithTop.coe_add] at ha
      have hc := selectedFinitePoleCount_add_compl F S ω T c
      change sLocalSelectedFinitePoleCount F S ω T c + sLocalSelectedFinitePoleCount F S ω U c =
        (sLocalFinitePolesAt F S ω c).card at hc
      have hi :
          (sLocalSelectedFinitePoleCount F S ω U c : ℤ) +
            ((sLocalSelectedFinitePoleCount F S ω T c : ℤ) - (sLocalPoleCount F S ω c : ℤ)) =
            -(sLocalArchPoleCount F S ω c : ℤ) := by
        rw [sLocalPoleCount]
        omega
      rwa [hi] at ha
    obtain ⟨g, hg⟩ := full_finiteImage_rep_of_arch_poles F S μ ν hν ω (P f) (fun c ↦
      (sLocalLaurentCoeff_vanish_iff F S μ ω c _ (P f)).mpr (hArch c))
    have hg' := g.property
    change g.val ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ at hg'
    rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace] at hg'
    obtain ⟨x, hx⟩ := hg'
    let y := sLocalWeilPrincipalValues F S T x
    have hUy : P y = g.val := by
      have hunion : U ∪ T = Finset.univ := by
        ext v
        by_cases hv : v ∈ T <;> simp [U, hv]
      have hdisj : Disjoint U T := by
        refine Finset.disjoint_left.mpr fun v hv hw ↦ ?_
        exact (Finset.mem_sdiff.mp hv).2 hw
      have hcomp : sLocalWeilPrincipalValues F S Finset.univ =
          P * sLocalWeilPrincipalValues F S T := by
        rw [← hunion]
        change (U ∪ T).noncommProd _ _ = U.noncommProd _ _ * T.noncommProd _ _
        exact Finset.noncommProd_union_of_disjoint hdisj _ _
      rw [← hx, hcomp]
      rfl
    have hzero : Zc (sLocalWeilPrincipalValues F S U (y - f)) = 0 := by
      change Zc (P (y - f)) = 0
      rw [map_sub, map_sub, hUy]
      exact sub_eq_zero.mpr hg
    have hcancel := sLocalPrincipalValues_cancel_meromorphic_zero F S μ ν hν ω U _ hzero
    have hy : M.mkQ y = M.mkQ f := by
      change Submodule.Quotient.mk (p := M) y = Submodule.Quotient.mk f
      rw [Submodule.Quotient.eq, mem_sLocalHomogeneousThetaKernel_iff,
        sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μ ν hν]
      exact hcancel
    refine ⟨y, ?_, hy⟩
    rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
    exact ⟨x, rfl⟩

include hν in
/-- The homogeneous range is the closed pole-bound subspace for any
selection of finite principal-value factors. -/
theorem sLocalFiniteNonzeroTestSubspace_map_eq_selected_poleBound
    (ω : PontryaginDual (K F S)) (T : Finset S) :
    (sLocalFiniteNonzeroTestSubspace F S T).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ =
      sLocalThetaPoleBound F S μ ν hν ω
        (fun c ↦ sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c) := by
  apply Submodule.ext
  intro q
  obtain ⟨f, rfl⟩ := (sLocalHomogeneousThetaKernel F S ν ω).mkQ_surjective q
  rw [sLocal_mk_mem_selected_finiteImage_iff_poleBound F S μ ν hν ω]
  change _ ↔ (Submodule.Quotient.mk f : SLocalHomogeneousThetaQuotient F S ν ω) ∈ _
  rw [mem_sLocalThetaPoleBound_mk]
  apply forall_congr'
  intro c
  rw [Nat.cast_sub (sLocalSelectedFinitePoleCount_le F S ω T c), neg_sub]

include hν in
theorem sLocalFiniteNonzeroTestSubspace_map_isClosed
    (ω : PontryaginDual (K F S)) (T : Finset S) :
    IsClosed ((sLocalFiniteNonzeroTestSubspace F S T).map
      (sLocalHomogeneousThetaKernel F S ν ω).mkQ : Set (SLocalHomogeneousThetaQuotient F S ν ω)) := by
  rw [sLocalFiniteNonzeroTestSubspace_map_eq_selected_poleBound F S μ ν hν ω T]
  exact sLocalThetaPoleBound_isClosed F S μ ν hν ω _

include hν in
/-- Proposition 7.2.2.1(1) and (3), with the printed finite band of
Laurent indices at each selected center. -/
theorem sLocal_mk_mem_selected_finiteImage_iff_removed_coefficients
    (ω : PontryaginDual (K F S)) (T : Finset S) (f : E F S) :
    (sLocalHomogeneousThetaKernel F S ν ω).mkQ f ∈
      (sLocalFiniteNonzeroTestSubspace F S T).map (sLocalHomogeneousThetaKernel F S ν ω).mkQ ↔
      ∀ c : ℂ, 0 < sLocalSelectedFinitePoleCount F S ω T c →
        ∀ k : ℕ, sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c < k →
          k ≤ sLocalPoleCount F S ω c → sLocalLaurentCoeff F S μ ω c k f = 0 := by
  rw [sLocal_mk_mem_selected_finiteImage_iff_poleBound F S μ ν hν ω]
  apply forall_congr'
  intro c
  let d := sLocalPoleCount F S ω c
  let t := sLocalSelectedFinitePoleCount F S ω T c
  have htd : t ≤ d := sLocalSelectedFinitePoleCount_le F S ω T c
  have hbound : ((-(d : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
    have h := sLocalZeta_poleOrder_le_euler F S μ ω f c
    rw [sLocalEulerFactor_order F S ω c, sLocalAllowedPoleOrder_eq_count F S ω c] at h
    exact h
  have he : ((-(d - t : ℕ) : ℤ) : WithTop ℤ) = (((t : ℤ) - (d : ℤ) : ℤ) : WithTop ℤ) := by
    rw [Nat.cast_sub htd, neg_sub]
  rw [← he, ← sLocalLaurentCoeff_vanish_iff F S μ ω c (d - t) f]
  constructor
  · exact fun h _ k hk _ ↦ h k hk
  · intro h k hk
    by_cases hkd : k ≤ d
    · exact h (by omega) k hk hkd
    · exact (sLocalLaurentCoeff_vanish_iff F S μ ω c d f).mpr hbound k (lt_of_not_ge hkd)

end

end Masullo
