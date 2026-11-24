import SLocalPrincipalValueImage
import Mathlib.Logic.Denumerable

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev R := {w : InfinitePlace F // w.IsReal}
private abbrev C := {w : InfinitePlace F // w.IsComplex}

private def realPoleCenter (ω : PontryaginDual (K F S)) (v : R F) (n : ℕ) : ℂ :=
  -(sLocalRealArchParameters F S ω v).1 -
    ((sLocalRealArchParameters F S ω v).2 % 2 : ℕ) - 2 * (n : ℂ)

private def complexPoleCenter (ω : PontryaginDual (K F S)) (v : C F) (n : ℕ) : ℂ :=
  -(sLocalComplexArchParameters F S ω v).1 -
    ((sLocalComplexArchParameters F S ω v).2.natAbs : ℂ) / 2 - (n : ℂ)

/-- The first `N v + 1` poles of each local Gamma factor, with
coincident centers included only once. -/
def sLocalArchPoleCutoff (ω : PontryaginDual (K F S)) (N : InfinitePlace F → ℕ) : Finset ℂ :=
  (Finset.univ.biUnion fun v : R F ↦ (Finset.range (N v.val + 1)).image (realPoleCenter F S ω v)) ∪
    (Finset.univ.biUnion fun v : C F ↦ (Finset.range (N v.val + 1)).image (complexPoleCenter F S ω v))

theorem mem_sLocalArchPoleCutoff (ω : PontryaginDual (K F S)) (N : InfinitePlace F → ℕ) (c : ℂ) :
    c ∈ sLocalArchPoleCutoff F S ω N ↔
      (∃ (v : R F) (n : ℕ), n ≤ N v.val ∧ c = realPoleCenter F S ω v n) ∨
      (∃ (v : C F) (n : ℕ), n ≤ N v.val ∧ c = complexPoleCenter F S ω v n) := by
  simp only [sLocalArchPoleCutoff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (⟨v, n, hn, he⟩ | ⟨v, n, hn, he⟩)
    · exact Or.inl ⟨v, n, hn, he.symm⟩
    · exact Or.inr ⟨v, n, hn, he.symm⟩
  · rintro (⟨v, n, hn, he⟩ | ⟨v, n, hn, he⟩)
    · exact Or.inl ⟨v, n, hn, he.symm⟩
    · exact Or.inr ⟨v, n, hn, he.symm⟩

theorem sLocalArchPoleCutoff_mono (ω : PontryaginDual (K F S)) :
    Monotone (sLocalArchPoleCutoff F S ω) := by
  intro N T h c hc
  rw [mem_sLocalArchPoleCutoff] at hc ⊢
  rcases hc with ⟨v, n, hn, hE⟩ | ⟨v, n, hn, hE⟩
  · exact Or.inl ⟨v, n, hn.trans (h v.val), hE⟩
  · exact Or.inr ⟨v, n, hn.trans (h v.val), hE⟩

private theorem sLocalArchPoleCount_pos_iff (ω : PontryaginDual (K F S)) (c : ℂ) :
    0 < sLocalArchPoleCount F S ω c ↔
      (∃ (v : R F) (n : ℕ), c = realPoleCenter F S ω v n) ∨
      (∃ (v : C F) (n : ℕ), c = complexPoleCenter F S ω v n) := by
  have hR (v : R F) :
      realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
        (c + (sLocalRealArchParameters F S ω v).1) = 0 ↔
        ∃ n, c = realPoleCenter F S ω v n := by
    rw [realArchZetaDenominator_eq_zero_iff]
    apply exists_congr
    intro n
    unfold realPoleCenter
    constructor <;> intro h <;> linear_combination h
  have hC (v : C F) :
      complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
        (c + (sLocalComplexArchParameters F S ω v).1) = 0 ↔
        ∃ n, c = complexPoleCenter F S ω v n := by
    rw [complexArchZetaDenominator_eq_zero_iff]
    apply exists_congr
    intro n
    unfold complexPoleCenter
    constructor <;> intro h <;> linear_combination h
  let r := Finset.univ.filter fun v : R F ↦
    realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
      (c + (sLocalRealArchParameters F S ω v).1) = 0
  let t := Finset.univ.filter fun v : C F ↦
    complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
      (c + (sLocalComplexArchParameters F S ω v).1) = 0
  change 0 < r.card + t.card ↔ _
  rw [show 0 < r.card + t.card ↔ 0 < r.card ∨ 0 < t.card by omega]
  simp only [r, t, Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and, hR, hC]

theorem sLocalArchPoleCount_pos_iff_exists_cutoff (ω : PontryaginDual (K F S)) (c : ℂ) :
    0 < sLocalArchPoleCount F S ω c ↔ ∃ n : ℕ, c ∈ sLocalArchPoleCutoff F S ω (fun _ ↦ n) := by
  rw [sLocalArchPoleCount_pos_iff]
  constructor
  · rintro (⟨v, n, h⟩ | ⟨v, n, h⟩)
    · exact ⟨n, (mem_sLocalArchPoleCutoff F S ω _ c).mpr (Or.inl ⟨v, n, le_rfl, h⟩)⟩
    · exact ⟨n, (mem_sLocalArchPoleCutoff F S ω _ c).mpr (Or.inr ⟨v, n, le_rfl, h⟩)⟩
  · intro ⟨n, hn⟩
    rcases (mem_sLocalArchPoleCutoff F S ω _ c).mp hn with ⟨v, j, _, h⟩ | ⟨v, j, _, h⟩
    · exact Or.inl ⟨v, j, h⟩
    · exact Or.inr ⟨v, j, h⟩

/-- Laurent indices at all archimedean pole centers of the component. -/
abbrev SLocalArchPoleIndex (ω : PontryaginDual (K F S)) :=
  {p : ℂ × ℕ // 0 < p.2 ∧ p.2 ≤ sLocalArchPoleCount F S ω p.1}

/-- A finite set of Laurent indices, with all coincident local orders retained. -/
abbrev SLocalArchCutoffIndex (ω : PontryaginDual (K F S)) (N : InfinitePlace F → ℕ) :=
  {p : SLocalArchPoleIndex F S ω // p.val.1 ∈ sLocalArchPoleCutoff F S ω N}

theorem sLocalArchCutoffIndex_finite (ω : PontryaginDual (K F S)) (N : InfinitePlace F → ℕ) :
    Finite (SLocalArchCutoffIndex F S ω N) := by
  let B : ℕ := Fintype.card (InfinitePlace F) + S.card
  letI : Fintype ↥(sLocalArchPoleCutoff F S ω N) := inferInstance
  let f (p : SLocalArchCutoffIndex F S ω N) : ↥(sLocalArchPoleCutoff F S ω N) × Fin (B+1) :=
    (⟨p.val.val.1, p.property⟩, ⟨p.val.val.2, Nat.lt_succ_of_le
      (p.val.property.2.trans ((Nat.le_add_right _ _ : sLocalArchPoleCount F S ω p.val.val.1 ≤
        sLocalPoleCount F S ω p.val.val.1).trans (sLocalPoleCount_le_places F S ω p.val.val.1)))⟩)
  apply Finite.of_injective f
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h)

/-- The indices can be enumerated by the natural numbers. Each number
field has an infinite place, whose local Gamma lattice is infinite. -/
theorem sLocalArchPoleIndex_enumerable (ω : PontryaginDual (K F S)) :
    Nonempty (ℕ ≃ SLocalArchPoleIndex F S ω) := by
  let A : Set ℂ := ⋃ n : ℕ, (sLocalArchPoleCutoff F S ω (fun _ ↦ n) : Set ℂ)
  letI : Countable A := (Set.countable_iUnion fun n ↦ (sLocalArchPoleCutoff F S ω
    (fun _ ↦ n)).finite_toSet.countable).to_subtype
  have hcount : Countable (SLocalArchPoleIndex F S ω) := by
    let f (x : SLocalArchPoleIndex F S ω) : A × ℕ :=
      (⟨x.val.1, Set.mem_iUnion.mpr
        ((sLocalArchPoleCount_pos_iff_exists_cutoff F S ω x.val.1).mp
          (x.property.1.trans_le x.property.2))⟩, x.val.2)
    apply Function.Injective.countable (f := f)
    intro x y h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z : A × ℕ ↦ z.2) h)
  have hInf : Infinite (SLocalArchPoleIndex F S ω) := by
    let v : InfinitePlace F := Classical.choice inferInstance
    rcases v.isReal_or_isComplex with h | h
    · let a : R F := ⟨v, h⟩
      let f (n : ℕ) : SLocalArchPoleIndex F S ω :=
        ⟨(realPoleCenter F S ω a n, 1), zero_lt_one,
          (sLocalArchPoleCount_pos_iff F S ω _).mpr (Or.inl ⟨a,n,rfl⟩)⟩
      apply Infinite.of_injective f
      intro n m h
      have he : realPoleCenter F S ω a n = realPoleCenter F S ω a m :=
        congrArg (Prod.fst ∘ Subtype.val) h
      unfold realPoleCenter at he
      have h' : (n : ℂ) = (m : ℂ) := by linear_combination (-1/2 : ℂ) * he
      exact_mod_cast h'
    · let a : C F := ⟨v, h⟩
      let f (n : ℕ) : SLocalArchPoleIndex F S ω :=
        ⟨(complexPoleCenter F S ω a n, 1), zero_lt_one,
          (sLocalArchPoleCount_pos_iff F S ω _).mpr (Or.inr ⟨a,n,rfl⟩)⟩
      apply Infinite.of_injective f
      intro n m h
      have he : complexPoleCenter F S ω a n = complexPoleCenter F S ω a m :=
        congrArg (Prod.fst ∘ Subtype.val) h
      unfold complexPoleCenter at he
      have h' : (n : ℂ) = (m : ℂ) := by linear_combination -he
      exact_mod_cast h'
  letI := hcount
  letI := hInf
  obtain ⟨hD⟩ := nonempty_denumerable (SLocalArchPoleIndex F S ω)
  letI := hD
  exact ⟨(Denumerable.eqv _).symm⟩

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (ν : Measure (K F S)) [ν.IsHaarMeasure]

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ)
  Measure.count (sLocalClassHaar F S ν))
variable (ω : PontryaginDual (K F S))

private abbrev V := sLocalArchPolarImage F S ν ω
private abbrev P := sLocalArchPolarKernel F S μ ν hν ω
private abbrev X := sLocalBruhatImage F S
private abbrev M := sLocalHomogeneousThetaKernel F S ν ω

/-- The actual Laurent functional restricted to the full finite principal-value image. -/
def sLocalArchLaurentCoeff (c : ℂ) (k : ℕ) : StrongDual ℂ (V F S ν ω) :=
  (sLocalThetaLaurentCoeff F S μ ν hν ω c k).comp (V F S ν ω).subtypeL

include hν in
private theorem exists_principalValue_rep (q : V F S ν ω) :
    ∃ f : X F S, (M F S ν ω).mkQ (sLocalWeilPrincipalValues F S Finset.univ f) = q.val := by
  have h := (sLocalFiniteNonzeroTestSubspace_images F S μ ν hν ω).2
  have hq : q.val ∈ ((sLocalFiniteNonzeroTestSubspace F S Finset.univ).map
      (M F S ν ω).mkQ : Set (SLocalHomogeneousThetaQuotient F S ν ω)) := q.property
  rwa [h] at hq

set_option maxHeartbeats 1600000 in
/-- Coefficients beyond the archimedean bound vanish identically on that image. -/
theorem sLocalArchLaurentCoeff_eq_zero_of_lt {c : ℂ} {k : ℕ}
    (hk : sLocalArchPoleCount F S ω c < k) (q : V F S ν ω) :
    sLocalArchLaurentCoeff F S μ ν hν ω c k q = 0 := by
  obtain ⟨f, hf⟩ := exists_principalValue_rep F S μ ν hν ω q
  change sLocalThetaLaurentCoeff F S μ ν hν ω c k q.val = 0
  rw [← hf]
  exact (sLocalLaurentCoeff_vanish_iff F S μ ω c (sLocalArchPoleCount F S ω c)
      (sLocalWeilPrincipalValues F S Finset.univ f)).mpr
    (sLocalWeilPrincipalValues_archPoleBound F S μ ν hν ω f c) k hk

/-- Simultaneous extraction of the coefficients at a finite cutoff. -/
def sLocalArchCutoffCoefficients (N : InfinitePlace F → ℕ) :
    V F S ν ω →L[ℂ] (SLocalArchCutoffIndex F S ω N → ℂ) :=
  ContinuousLinearMap.pi fun i ↦
    sLocalArchLaurentCoeff F S μ ν hν ω i.val.val.1 i.val.val.2

/-- The stage with no pole at any of the cutoff centers. -/
def sLocalArchPoleFiltration (N : InfinitePlace F → ℕ) : Submodule ℂ (V F S ν ω) :=
  (sLocalArchCutoffCoefficients F S μ ν hν ω N).ker

theorem mem_sLocalArchPoleFiltration (N : InfinitePlace F → ℕ) (q : V F S ν ω) :
    q ∈ sLocalArchPoleFiltration F S μ ν hν ω N ↔
      ∀ (c : ℂ), c ∈ sLocalArchPoleCutoff F S ω N →
        ∀ k > 0, sLocalArchLaurentCoeff F S μ ν hν ω c k q = 0 := by
  constructor
  · intro h c hc k hk
    by_cases hle : k ≤ sLocalArchPoleCount F S ω c
    · have h0 : sLocalArchCutoffCoefficients F S μ ν hν ω N q = 0 := h
      exact congrFun h0 ⟨⟨(c,k), hk, hle⟩, hc⟩
    · exact sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω (lt_of_not_ge hle) q
  · intro h
    change sLocalArchCutoffCoefficients F S μ ν hν ω N q = 0
    funext i
    exact h i.val.val.1 i.property i.val.val.2 i.val.property.1

theorem sLocalArchPoleFiltration_antitone : Antitone (sLocalArchPoleFiltration F S μ ν hν ω) := by
  intro N T h q hq
  apply (mem_sLocalArchPoleFiltration F S μ ν hν ω N q).mpr
  intro c hc
  exact (mem_sLocalArchPoleFiltration F S μ ν hν ω T q).mp hq c
    (sLocalArchPoleCutoff_mono F S ω h hc)

theorem sLocalArchPoleFiltration_isClosed (N : InfinitePlace F → ℕ) :
    IsClosed (sLocalArchPoleFiltration F S μ ν hν ω N : Set (V F S ν ω)) :=
  (sLocalArchCutoffCoefficients F S μ ν hν ω N).isClosed_ker

private theorem mem_sLocalArchPolarKernel (q : V F S ν ω) :
    q ∈ P F S μ ν hν ω ↔ ∀ c k, 0 < k → sLocalArchLaurentCoeff F S μ ν hν ω c k q = 0 := by
  obtain ⟨f, hf⟩ := exists_principalValue_rep F S μ ν hν ω q
  let g := sLocalWeilPrincipalValues F S Finset.univ f
  change q.val ∈ sLocalThetaPoleBound F S μ ν hν ω (fun _ ↦ 0) ↔ _
  rw [← hf]
  change (Submodule.Quotient.mk g : SLocalHomogeneousThetaQuotient F S ν ω) ∈
    sLocalThetaPoleBound F S μ ν hν ω (fun _ ↦ 0) ↔ _
  rw [mem_sLocalThetaPoleBound_mk]
  have he (c : ℂ) (k : ℕ) :
      sLocalArchLaurentCoeff F S μ ν hν ω c k q = sLocalLaurentCoeff F S μ ω c k g := by
    change sLocalThetaLaurentCoeff F S μ ν hν ω c k q.val = _
    rw [← hf]
    rfl
  constructor
  · intro h c k hk
    rw [he]
    exact (sLocalLaurentCoeff_vanish_iff F S μ ω c 0 g).mpr (by simpa using h c) k hk
  · intro h c
    have hc := (sLocalLaurentCoeff_vanish_iff F S μ ω c 0 g).mp
      (fun k hk ↦ (he c k).symm.trans (h c k hk))
    simpa using hc

/-- The intersection of the cutoff stages is the actual entire-Mellin subspace. -/
theorem sLocalArchPoleFiltration_iInf :
    (⨅ N : InfinitePlace F → ℕ, sLocalArchPoleFiltration F S μ ν hν ω N) =
      P F S μ ν hν ω := by
  apply Submodule.ext
  intro q
  rw [Submodule.mem_iInf, mem_sLocalArchPolarKernel]
  constructor
  · intro h c k hk
    by_cases hle : k ≤ sLocalArchPoleCount F S ω c
    · obtain ⟨n, hn⟩ := (sLocalArchPoleCount_pos_iff_exists_cutoff F S ω c).mp (hk.trans_le hle)
      exact (mem_sLocalArchPoleFiltration F S μ ν hν ω _ q).mp (h (fun _ ↦ n)) c hn k hk
    · exact sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω (lt_of_not_ge hle) q
  · intro h N
    exact (mem_sLocalArchPoleFiltration F S μ ν hν ω N q).mpr (fun c _ k hk ↦ h c k hk)

private abbrev Z (f : X F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- A finite filtration stage consists precisely of classes whose
continued Mellin transform is regular at every selected center. -/
theorem mem_sLocalArchPoleFiltration_iff_order (N : InfinitePlace F → ℕ) (q : V F S ν ω)
    (f : X F S) (hf : (M F S ν ω).mkQ f = q.val) :
    q ∈ sLocalArchPoleFiltration F S μ ν hν ω N ↔
      ∀ c ∈ sLocalArchPoleCutoff F S ω N, 0 ≤ meromorphicOrderAt (Z F S μ ω f) c := by
  have he (c : ℂ) (k : ℕ) :
      sLocalArchLaurentCoeff F S μ ν hν ω c k q = sLocalLaurentCoeff F S μ ω c k f := by
    change sLocalThetaLaurentCoeff F S μ ν hν ω c k q.val = _
    rw [← hf]
    rfl
  rw [mem_sLocalArchPoleFiltration]
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro _
  simpa only [he, Nat.cast_zero, neg_zero, WithTop.coe_zero] using
    (sLocalLaurentCoeff_vanish_iff F S μ ω c 0 f)

/-- The zero-pole kernel in the archimedean image is exactly the entire
continuation after normalizing the representative at removable points. -/
theorem mem_sLocalArchPolarKernel_iff_entire (q : V F S ν ω) (f : X F S)
    (hf : (M F S ν ω).mkQ f = q.val) :
    q ∈ P F S μ ν hν ω ↔
      AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) univ := by
  change q.val ∈ sLocalThetaPoleBound F S μ ν hν ω (fun _ ↦ 0) ↔ _
  rw [← hf]
  change (Submodule.Quotient.mk f : SLocalHomogeneousThetaQuotient F S ν ω) ∈
    sLocalThetaPoleBound F S μ ν hν ω (fun _ ↦ 0) ↔ _
  rw [mem_sLocalThetaPoleBound_mk]
  let g := Z F S μ ω f
  have hm : MeromorphicOn g univ := (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f).meromorphicOn
  constructor
  · intro h c hc
    apply (meromorphicNFOn_toMeromorphicNFOn g univ hc).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hc]
    simpa using h c
  · intro h c
    have hc := (h c (mem_univ c)).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ c)] at hc
    simpa using hc

private theorem finiteCoefficient_annihilator {V I : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [Fintype I] (a : I → StrongDual ℂ V) :
    let A := ContinuousLinearMap.pi a
    Set.range (fun l : StrongDual ℂ (V ⧸ A.ker) ↦ l.comp A.ker.mkQL) =
      (Submodule.span ℂ (Set.range a) : Set (StrongDual ℂ V)) := by
  intro A
  apply Set.ext
  intro L
  constructor
  · rintro ⟨l, rfl⟩
    let g := (l.comp A.ker.mkQL).toLinearMap
    have hg : g ∈ A.ker.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro x hx
      change l (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).mpr hx, map_zero]
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker A.toLinearMap] at hg
    obtain ⟨b, hb⟩ := hg
    refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun i ↦ b (Pi.single i 1), ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    have hbx : b (A x) = l ((A.ker).mkQ x) := DFunLike.congr_fun hb x
    change (∑ i, b (Pi.single i 1) • a i) x = l ((A.ker).mkQ x)
    rw [← hbx]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    change ∑ i, b (Pi.single i 1) * (A x i) = b (A x)
    have he : A x = ∑ i : I, Pi.single i (A x i) := by
      funext i
      rw [Finset.sum_apply]
      exact (Fintype.sum_pi_single i (A x)).symm
    conv_rhs => rw [he]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : (A x i) • Pi.single i (1 : ℂ) = Pi.single i (A x i) := by
      funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne h]
    rw [← hs, map_smul, smul_eq_mul, mul_comm]
  · intro h
    have hK : A.ker ≤ L.ker := by
      intro x hx
      have hx0 : A x = 0 := hx
      have hcoeff (i : I) : a i x = 0 := congrFun hx0 i
      have hspan : ∀ f ∈ Submodule.span ℂ (Set.range a), f x = 0 := by
        intro f hf
        induction hf using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨i, rfl⟩ := hf
          exact hcoeff i
        | zero => rfl
        | add f g _ _ hf hg =>
          change f x + g x = 0
          rw [hf, hg, add_zero]
        | smul t f _ hf =>
          change t * f x = 0
          rw [hf, mul_zero]
      exact hspan L h
    exact ⟨A.ker.liftQL L hK, ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-- On a finite stage the selected coefficient functionals span exactly
the pullback of the continuous dual of the stage quotient. -/
theorem sLocalArchPoleFiltration_dualSpan (N : InfinitePlace F → ℕ) :
    let T := sLocalArchPoleFiltration F S μ ν hν ω N
    Set.range (fun l : StrongDual ℂ (V F S ν ω ⧸ T) ↦ l.comp T.mkQL) =
      (Submodule.span ℂ (Set.range fun i : SLocalArchCutoffIndex F S ω N ↦
        sLocalArchLaurentCoeff F S μ ν hν ω i.val.val.1 i.val.val.2) :
        Set (StrongDual ℂ (V F S ν ω))) := by
  letI := sLocalArchCutoffIndex_finite F S ω N
  letI := Fintype.ofFinite (SLocalArchCutoffIndex F S ω N)
  exact finiteCoefficient_annihilator fun i : SLocalArchCutoffIndex F S ω N ↦
    sLocalArchLaurentCoeff F S μ ν hν ω i.val.val.1 i.val.val.2

/-- The finite quotient carries exactly the topology of its attained
coefficient vectors. Its inverse is continuous by finite dimensionality. -/
def sLocalArchPoleFiltration_equiv_range (N : InfinitePlace F → ℕ) :
    (V F S ν ω ⧸ sLocalArchPoleFiltration F S μ ν hν ω N) ≃L[ℂ]
      (sLocalArchCutoffCoefficients F S μ ν hν ω N).range := by
  let A := sLocalArchCutoffCoefficients F S μ ν hν ω N
  let T := sLocalArchPoleFiltration F S μ ν hν ω N
  letI := sLocalArchCutoffIndex_finite F S ω N
  letI := Fintype.ofFinite (SLocalArchCutoffIndex F S ω N)
  letI : FiniteDimensional ℂ A.range := inferInstance
  let e : (V F S ν ω ⧸ T) ≃ₗ[ℂ] A.range := A.toLinearMap.quotKerEquivRange
  letI : FiniteDimensional ℂ (V F S ν ω ⧸ T) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : IsClosed (T : Set (V F S ν ω)) := sLocalArchPoleFiltration_isClosed F S μ ν hν ω N
  letI : T3Space (V F S ν ω ⧸ T) := Submodule.t3_quotient_of_isClosed T
  letI : T2Space (V F S ν ω ⧸ T) := inferInstance
  exact e.toContinuousLinearEquiv

@[simp] theorem sLocalArchPoleFiltration_equiv_range_mk (N : InfinitePlace F → ℕ) (q : V F S ν ω) :
    (sLocalArchPoleFiltration_equiv_range F S μ ν hν ω N (Submodule.Quotient.mk q)).val =
      sLocalArchCutoffCoefficients F S μ ν hν ω N q := rfl

/-- The archimedean quotient maps continuously into the full coefficient product. -/
def sLocalArchPolarQuotientCoefficients :
    (V F S ν ω ⧸ P F S μ ν hν ω) →L[ℂ] (SLocalArchPoleIndex F S ω → ℂ) := by
  let A : V F S ν ω →L[ℂ] (SLocalArchPoleIndex F S ω → ℂ) :=
    ContinuousLinearMap.pi fun i ↦ sLocalArchLaurentCoeff F S μ ν hν ω i.val.1 i.val.2
  refine (P F S μ ν hν ω).liftQL A ?_
  intro q hq
  change A q = 0
  funext i
  exact (mem_sLocalArchPolarKernel F S μ ν hν ω q).mp hq i.val.1 i.val.2 i.property.1

/-- Every archimedean coefficient together separates the entire-Mellin classes. -/
theorem sLocalArchPolarQuotientCoefficients_injective :
    Injective (sLocalArchPolarQuotientCoefficients F S μ ν hν ω) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (P F S μ ν hν ω) q
  intro h
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (mem_sLocalArchPolarKernel F S μ ν hν ω f).mpr
  intro c k hk
  by_cases hle : k ≤ sLocalArchPoleCount F S ω c
  · exact congrFun h ⟨(c,k), hk, hle⟩
  · exact sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω (lt_of_not_ge hle) f

/-- The canonical quotient map from all archimedean coefficients to a finite stage. -/
def sLocalArchPolarToCutoff (N : InfinitePlace F → ℕ) :
    (V F S ν ω ⧸ P F S μ ν hν ω) →L[ℂ]
      (V F S ν ω ⧸ sLocalArchPoleFiltration F S μ ν hν ω N) := by
  let T := sLocalArchPoleFiltration F S μ ν hν ω N
  apply (P F S μ ν hν ω).liftQL T.mkQL
  intro q hq
  change T.mkQ q = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hp := (mem_sLocalArchPolarKernel F S μ ν hν ω q).mp hq
  exact (mem_sLocalArchPoleFiltration F S μ ν hν ω N q).mpr (fun c _ k hk ↦ hp c k hk)

theorem sLocalArchPolarToCutoff_surjective (N : InfinitePlace F → ℕ) :
    Surjective (sLocalArchPolarToCutoff F S μ ν hν ω N) := by
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (sLocalArchPoleFiltration F S μ ν hν ω N) q
  exact ⟨(P F S μ ν hν ω).mkQ v, rfl⟩

theorem sLocalArchPolarToCutoff_isOpenMap (N : InfinitePlace F → ℕ) :
    IsOpenMap (sLocalArchPolarToCutoff F S μ ν hν ω N) :=
  IsOpenMap.of_comp (P F S μ ν hν ω).mkQL.continuous
    (Submodule.Quotient.mk_surjective (P F S μ ν hν ω))
    (sLocalArchPoleFiltration F S μ ν hν ω N).isOpenQuotientMap_mkQL.isOpenMap

/-- The canonical maps to the finite quotients jointly separate the polar quotient. -/
theorem sLocalArchPolarToCutoff_joint_injective :
    Injective (ContinuousLinearMap.pi (sLocalArchPolarToCutoff F S μ ν hν ω)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (P F S μ ν hν ω) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← sLocalArchPoleFiltration_iInf F S μ ν hν ω, Submodule.mem_iInf]
  intro N
  exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun hq N)

end

end Masullo
