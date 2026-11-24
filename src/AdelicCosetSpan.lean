import BruhatCosetIndicators
import SLocalBruhatFiniteTensor
import Mathlib.Algebra.BigOperators.Ring.Finset

open Function IsDedekindDomain NumberField Set Topology
open scoped BigOperators Classical NumberField RestrictedProduct SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Coord (S : Finset (Place F)) := (w : S) → w.val.adicCompletion F

/-- The translated fractional-ideal ball in a finite completion. -/
def finitePlaceTranslatedBall (w : Place F) (a : w.adicCompletion F) (N : ℤ) :
    Set (w.adicCompletion F) :=
  {x | ∃ z : w.adicCompletionIntegers F, x =
    a + (chosenFiniteUniformizer F w : w.adicCompletion F) ^ N * z.val}

theorem finitePlaceTranslatedBall_compactOpen (w : Place F) (a : w.adicCompletion F) (N : ℤ) :
    IsCompact (finitePlaceTranslatedBall F w a N) ∧ IsOpen (finitePlaceTranslatedBall F w a N) := by
  let π : w.adicCompletion F := chosenFiniteUniformizer F w
  let e := (Homeomorph.mulLeft₀ (π ^ N) (zpow_ne_zero _ (Units.ne_zero _))).trans
    (Homeomorph.addLeft a)
  have he : e '' (w.adicCompletionIntegers F : Set (w.adicCompletion F)) =
      finitePlaceTranslatedBall F w a N := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
  rw [← he]
  letI := compactSpace_adicIntegers w
  have hc : IsCompact (w.adicCompletionIntegers F : Set (w.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr inferInstance
  exact ⟨hc.image e.continuous, e.isOpenMap _ (Valued.isOpen_valuationSubring _)⟩

/-- Every ball used in the expansion is a translate of a compact open additive subgroup. -/
theorem finitePlaceTranslatedBall_isCoset (w : Place F) (a : w.adicCompletion F) (N : ℤ) :
    ∃ H : AddSubgroup (w.adicCompletion F),
      IsCompact (H : Set (w.adicCompletion F)) ∧ IsOpen (H : Set (w.adicCompletion F)) ∧
        finitePlaceTranslatedBall F w a N = (a + ·) '' (H : Set (w.adicCompletion F)) := by
  let q := (chosenFiniteUniformizer F w : w.adicCompletion F) ^ N
  let H := (w.adicCompletionIntegers F).toAddSubgroup.map (AddMonoidHom.mulLeft q)
  have hzero : (H : Set (w.adicCompletion F)) = finitePlaceTranslatedBall F w 0 N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, (zero_add _).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, (zero_add _).symm⟩
  have hH := hzero ▸ finitePlaceTranslatedBall_compactOpen F w 0 N
  refine ⟨H, hH.1, hH.2, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨q * y.val, ⟨y.val, y.property, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

private def cosetTest (w : Place F) (a : w.adicCompletion F) (N : ℤ) :
    locallyConstantTests (w.adicCompletion F) :=
  compactOpenIndicator (w.adicCompletion F) ⟨finitePlaceTranslatedBall F w a N,
    finitePlaceTranslatedBall_compactOpen F w a N⟩

/-- A Schwartz factor times an adelic rectangle of translated ideal balls,
with the integer ring at each place outside the finite set. -/
def globalBruhatCosetTensor (S : Finset (Place F)) (φ : Arch F) (a : Coord F S) (N : S → ℤ) :
    GlobalBruhat F :=
  (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
    (fun w => cosetTest F w.val (a w) (N w)))).val

theorem globalBruhatCosetTensor_apply (S : Finset (Place F))
    (φ : Arch F) (a : Coord F S) (N : S → ℤ) (x : Adeles F) :
    GlobalBruhat.evaluation F x (globalBruhatCosetTensor F S φ a N) =
      (φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
        ∏ w : S, (finitePlaceTranslatedBall F w.val (a w) (N w)).indicator
          (fun _ => (1 : ℂ)) (x.2 w.val)) *
        if ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F then 1 else 0 := by
  unfold globalBruhatCosetTensor
  rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply]
  rfl

/-- Data indexing the translated rectangles used in the corrected expansion. -/
abbrev AdelicCosetIndex := Σ S : Finset (Place F), Arch F × Coord F S × (S → ℤ)

def adelicCosetTerm (d : AdelicCosetIndex F) : GlobalBruhat F :=
  globalBruhatCosetTensor F d.1 d.2.1 d.2.2.1 d.2.2.2

private theorem sLocalBruhatPure_mem_cosetSpan (S : Finset (Place F)) (φ : Arch F)
    (ψ : locallyConstantTests (Coord F S)) :
    (sLocalBruhatPure F S φ ψ).val ∈ Submodule.span ℂ (range (adelicCosetTerm F)) := by
  let U := Submodule.span ℂ (range (adelicCosetTerm F))
  let L := (sLocalBruhatImage F S).subtype.comp (sLocalBruhatPure F S φ)
  change L ψ ∈ U
  have hspan : Submodule.span ℂ (range (locallyConstantTestPiProduct
      (X := fun w : S => w.val.adicCompletion F))) ≤ U.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change L (locallyConstantTestPiProduct g) ∈ U
    choose n c a N hN h using
      fun w : S => finitePlaceSchwartz_sum_indicators F w.val (g w) (chosenFiniteUniformizer F w.val)
        (chosenFiniteUniformizer_spec F w.val)
    let term (j : ∀ w : S, Fin (n w)) : GlobalBruhat F :=
      adelicCosetTerm F ⟨S, φ, fun w => a w (j w), N⟩
    have ht (j : ∀ w : S, Fin (n w)) : term j ∈ U :=
      Submodule.subset_span ⟨_, rfl⟩
    have he : L (locallyConstantTestPiProduct g) =
        ∑ j : (∀ w : S, Fin (n w)), (∏ w : S, c w (j w)) • term j := by
      apply (GlobalBruhat.algebraicEquiv F).injective
      apply Subtype.ext
      funext x
      change GlobalBruhat.evaluation F x (L (locallyConstantTestPiProduct g)) =
        GlobalBruhat.evaluation F x (∑ j : (∀ w : S, Fin (n w)), (∏ w : S, c w (j w)) • term j)
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      have hleft : GlobalBruhat.evaluation F x (L (locallyConstantTestPiProduct g)) =
          (φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * ∏ w : S, (g w).val (x.2 w.val)) *
            if ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F then 1 else 0 := by
        change GlobalBruhat.evaluation F x (sLocalBruhatPure F S φ _).val = _
        rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatPure_restrict,
          locallyConstantTestPiProduct_apply]
        rfl
      simp_rw [hleft, h, term, adelicCosetTerm, globalBruhatCosetTensor_apply]
      rw [Fintype.prod_sum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.prod_mul_distrib]
      unfold finitePlaceTranslatedBall
      ring
    rw [he]
    exact U.sum_mem fun j _ => U.smul_mem _ (ht j)
  apply hspan
  rw [locallyConstantTest_span_piProduct]
  exact Submodule.mem_top

/-- Corrected Lemma 2.1.3.2(3). Every global test is in the complex span of
Schwartz factors times finite-place rectangles of translated ideal balls. -/
theorem globalBruhat_span_cosetTensors :
    Submodule.span ℂ (range (adelicCosetTerm F)) = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨S, g, rfl⟩ := globalBruhat_exhausted F f
  let B : Type _ := locallyConstantTests (Coord F S)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (Arch F ⊗[ℂ] B) := inductiveTensorTopology (Arch F) B
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨u, rfl⟩ := e.surjective g
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    have h : e (φ ⊗ₜ[ℂ] ψ) = sLocalBruhatPure F S φ ψ :=
      TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) φ ψ
    rw [h]
    exact sLocalBruhatPure_mem_cosetSpan F S φ ψ
  | add u v hu hv =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hu hv

/-- The corrected expansion as a finitely supported sum of actual test functions. -/
theorem globalBruhat_exists_cosetExpansion (f : GlobalBruhat F) :
    ∃ c : AdelicCosetIndex F →₀ ℂ, c.sum (fun d z => z • adelicCosetTerm F d) = f := by
  have h : f ∈ Submodule.span ℂ (range (adelicCosetTerm F)) := by
    rw [globalBruhat_span_cosetTensors]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h
  exact ⟨c, hc⟩

/-- A nonempty finite indexing of the expansion, including for the zero test. -/
theorem globalBruhat_exists_numberedCosetExpansion (f : GlobalBruhat F) :
    ∃ (r : ℕ) (c : Fin r → ℂ) (d : Fin r → AdelicCosetIndex F),
      0 < r ∧ (∑ i, c i • adelicCosetTerm F (d i)) = f := by
  obtain ⟨c, hc⟩ := globalBruhat_exists_cosetExpansion F f
  let J := Option ↥c.support
  let e := Fintype.equivFin J
  let d₀ : AdelicCosetIndex F := ⟨∅, 0, 0, 0⟩
  let d : J → AdelicCosetIndex F := fun i => i.elim d₀ Subtype.val
  let k : J → ℂ := fun i => i.elim 0 (fun j => c j.val)
  refine ⟨Fintype.card J, k ∘ e.symm, d ∘ e.symm, Fintype.card_pos, ?_⟩
  have he := e.symm.sum_comp (fun i : J => k i • adelicCosetTerm F (d i))
  change (∑ i, k (e.symm i) • adelicCosetTerm F (d (e.symm i))) = f
  rw [he, Fintype.sum_option]
  change 0 • adelicCosetTerm F d₀ + (∑ j : ↥c.support, c j.val • adelicCosetTerm F j.val) = f
  rw [zero_smul, zero_add]
  exact (Finset.sum_attach c.support (fun j => c j • adelicCosetTerm F j)).trans hc

end
end Masullo
