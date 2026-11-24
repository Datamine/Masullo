import PrintedOrbitalIndentation
import GlobalSobolevPrincipalValues
import BruhatCompactTestTopology

open Function MeasureTheory NumberField IsDedekindDomain Set Topology
open scoped NumberField

namespace Masullo
noncomputable section

private theorem bruhatSmooth_logProfile {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* Multiplicative ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) :
    (fun x ↦ f (m x).toAdd) ∈ bruhatSmoothSubmodule (G := G) := by
  intro j
  obtain ⟨P, _, _⟩ := pontryaginDual_mem_bruhatSmooth (1 : PontryaginDual G) j
  refine ⟨P, ?_, fun Q hQ q ↦ ?_⟩
  · intro k x
    change f (m (k.val * x)).toAdd = f (m x).toAdd
    rw [map_mul, P.modulation_eq_one_on_kernel m k, one_mul]
  let A := ElementaryLCAModel q.realDim q.torusDim q.latticeRank q.finiteFactor
  let M := (Q.descendHom m (Q.modulation_eq_one_on_kernel m)).comp
    (q.equiv.symm : Multiplicative A →ₜ* Q.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  refine ⟨f ∘ l, fun x ↦ ?_, fun a z ↦ ?_⟩
  · have he : l (Q.stageCoordinates q x).toAdd = (m x.val).toAdd := by
      change ((Q.descendHom m (Q.modulation_eq_one_on_kernel m))
        (q.equiv.symm (q.equiv (QuotientGroup.mk x)))).toAdd = _
      rw [q.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
    exact congrArg f he
  · let X := EuclideanSpace ℝ (Fin q.realDim) × EuclideanSpace ℝ (Fin q.torusDim)
    let H := l.comp (elementaryCoverHom : X →+ A)
    have hH : Continuous H := hl.comp elementaryCoverHom_continuous
    let H₀ := H.toRealLinearMap hH
    let L : X →L[ℝ] ℝ := ⟨H₀, H₀.continuous_of_finiteDimensional⟩
    have he : (fun u : X => l (elementaryCover u a z)) =
        fun u => L u + l (elementaryCover (0 : X) a z) := by
      funext u
      have he := elementaryCover_add (0 : X) u a z
      rw [zero_add] at he
      rw [he, map_add, add_comm]
      rfl
    change ContDiff ℝ j (f ∘ fun u : X ↦ l (elementaryCover u a z))
    rw [he]
    have hj : (j : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) := WithTop.coe_le_coe.mpr le_top
    exact (hf.of_le hj).comp (L.contDiff.add contDiff_const)

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev r (x : Q F) := (ideleClassLogNorm F x).toAdd

local instance shellWitnessQHausdorff : T2Space (Q F) := ideleClasses_hausdorff
local instance shellWitnessQLocallyCompact : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance shellWitnessKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

private theorem logNorm_proper : IsProperMap (r F) := by
  have he : r F = Prod.fst ∘ (ideleClassLogCoordinates F).symm := rfl
  rw [he]
  exact isProperMap_fst_of_compactSpace.comp (ideleClassLogCoordinates F).symm.isProperMap

private theorem globalUniformizer_logNorm (v : Place F) :
    r F (globalUniformizerClass F v) = -Real.log (v.asIdeal.absNorm : ℝ) := by
  change Real.log (ideleClassNorm F
    (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) = _
  rw [ideleClassNorm_mk, singleFiniteIdele_norm, norm_finiteUniformizer F v _
    (chosenFiniteUniformizer_spec F v), Real.log_inv]

private theorem realProfile_test (f : ℝ → ℂ) (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hfc : HasCompactSupport f) : ∃ φ : BruhatCompactTest (Q F), φ.val.val = f ∘ r F := by
  apply (exists_bruhatCompactTest_iff _).mpr
  refine ⟨?_,?_⟩
  · let m : Q F →ₜ* Multiplicative ℝ := ⟨ideleClassLogNorm F,ideleClassLogNorm_continuous F⟩
    exact bruhatSmooth_logProfile (G := Q F) m f hf
  have hc := (logNorm_proper F).isCompact_preimage hfc
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport f).preimage (logNorm_proper F).continuous)
  exact fun x hx ↦ subset_closure hx

/-- A radial compact Bruhat bump isolates the inverse uniformizer sample
at a single place. Its support lies strictly above norm one. -/
theorem exists_orbitalShell_single_sample (v : Place F) :
    ∃ φ : BruhatCompactTest (Q F),
      (∀ g : Q F, g ∈ tsupport φ.val.val → 1 < ideleClassNorm F g) ∧
      (∀ k : K F, ∀ g : Q F, φ.val.val (k.val * g) = φ.val.val g) ∧
      ∀ n : ℤ, φ.val.val (globalUniformizerClass F v ^ n) = if n = -1 then 1 else 0 := by
  let L := Real.log (v.asIdeal.absNorm : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  let b : ContDiffBump L := ⟨L/4,L/2,by positivity,by linarith⟩
  let f (x : ℝ) : ℂ := b x
  have hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hfc : HasCompactSupport f := b.hasCompactSupport.comp_left Complex.ofReal_zero
  obtain ⟨φ,hφ⟩ := realProfile_test F f hf hfc
  have hfs : tsupport f ⊆ Metric.closedBall L (L/2) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    have hb : x ∈ support b := by
      intro hz
      exact hx (by simp [f, show b x = 0 from hz])
    rw [b.support_eq] at hb
    exact Metric.ball_subset_closedBall hb
  refine ⟨φ,?_,?_,?_⟩
  · intro g hg
    have he : tsupport φ.val.val ⊆ (r F) ⁻¹' Metric.closedBall L (L/2) := by
      rw [hφ]
      apply closure_minimal _ (Metric.isClosed_closedBall.preimage (logNorm_proper F).continuous)
      exact fun x hx ↦ hfs (subset_closure hx)
    have hb := Metric.mem_closedBall.mp (he hg)
    rw [Real.dist_eq] at hb
    have hr : 0 < r F g := by linarith [neg_abs_le (r F g - L)]
    exact Real.log_pos_iff (ideleClassNorm_pos F g).le |>.mp hr
  · intro k g
    have hk : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = _
      rw [k.property, Real.log_one]
      rfl
    have h : r F (k.val * g) = r F g := by
      change ((ideleClassLogNorm F) (k.val * g)).toAdd = _
      rw [map_mul, hk, one_mul]
    rw [hφ]
    exact congrArg f h
  · intro n
    have hs (n : ℤ) : r F (globalUniformizerClass F v ^ n) = -(n : ℝ) * L := by
      change ((ideleClassLogNorm F) (globalUniformizerClass F v ^ n)).toAdd = _
      rw [map_zpow,toAdd_zpow,zsmul_eq_mul]
      change (n : ℝ) * r F (globalUniformizerClass F v) = _
      rw [globalUniformizer_logNorm]
      dsimp [L]
      ring
    by_cases hn : n = -1
    · subst n
      rw [ite_eq_left rfl, hφ]
      change f (r F (globalUniformizerClass F v ^ (-1 : ℤ))) = 1
      rw [hs]
      have he : -((-1 : ℤ) : ℝ) * L = L := by norm_num
      rw [he]
      change ((b L : ℝ) : ℂ) = 1
      exact_mod_cast b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    · rw [ite_eq_right hn, hφ]
      change f (r F (globalUniformizerClass F v ^ n)) = 0
      by_contra hne
      have hb := Metric.mem_closedBall.mp (hfs (subset_closure hne))
      rw [Real.dist_eq, hs, show -(n : ℝ) * L - L = (-(n : ℝ) - 1) * L by ring,
        abs_mul, abs_of_pos hL] at hb
      have hi : 1 ≤ |-(n : ℤ) - 1| := by
        have hne' : -(n : ℤ) - 1 ≠ 0 := by omega
        exact Int.one_le_abs hne'
      have hi' : (1 : ℝ) ≤ |-(n : ℝ) - 1| := by exact_mod_cast hi
      nlinarith [mul_le_mul_of_nonneg_right hi' hL.le]

/-- The isolated inverse-uniformizer sample gives a sum of one. -/
theorem exists_orbitalShell_sample_one (v : Place F) :
    ∃ φ : BruhatCompactTest (Q F),
      (∀ g : Q F, g ∈ tsupport φ.val.val → 1 < ideleClassNorm F g) ∧
      (∀ k : K F, ∀ g : Q F, φ.val.val (k.val * g) = φ.val.val g) ∧
      (∑' n : ℤ, φ.val.val (globalUniformizerClass F v ^ n)) = 1 := by
  obtain ⟨φ, hs, hinv, hsample⟩ := exists_orbitalShell_single_sample F v
  exact ⟨φ, hs, hinv, by simp [hsample]⟩

/-- The literal single-place equation (11.3.2.1) fails with the canonical
section. The counterexample test is invariant under all norm-one classes,
and the failure holds for any kernel used on its left-hand side. -/
theorem printedOrbitalShellEquation_counterexample
    [MeasurableSpace ((ideleLogNorm F).ker)] [MeasurableSpace (Multiplicative ℝ)]
    (η : Measure ((ideleLogNorm F).ker)) (E : Set ((ideleLogNorm F).ker))
    (dt : Measure (Multiplicative ℝ)) (A B : Finset (Place F))
    (v : Place F) (unitMass : ℝ) (hMass : 0 < unitMass) :
    ∃ φ : BruhatCompactTest (Q F),
      (∀ g : Q F, g ∈ tsupport φ.val.val → 1 < ideleClassNorm F g) ∧
      (∀ k : K F, ∀ g : Q F, φ.val.val (k.val * g) = φ.val.val g) ∧
      ∀ (K₀ : Idele F → Idele F → ℂ),
        (∑' ξ : Fˣ, ∫ t, ∫ g in E,
          let x := ideleExpSection F t
          let y := principalIdele F ξ * g.val * x
          ((orbitalDivisorialIndicator F B y - orbitalDivisorialIndicator F A y : ℝ) : ℂ) *
            (printedOrbitalSectionWeight F η E (ideleExpSection F) x y : ℂ) * K₀ x y ∂η ∂dt) ≠
        ((Real.log (v.asIdeal.absNorm : ℝ) / unitMass : ℝ) : ℂ) *
          ∑' n : ℤ, φ.val.val (globalUniformizerClass F v ^ n) := by
  obtain ⟨φ,hs,hInv,hSum⟩ := exists_orbitalShell_sample_one F v
  refine ⟨φ,hs,hInv,fun K₀ ↦ ?_⟩
  rw [printedOrbitalShellIntegral_eq_zero F η E dt A B K₀,hSum,mul_one]
  have hLog : 0 < Real.log (v.asIdeal.absNorm : ℝ) :=
    Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  exact (Complex.ofReal_ne_zero.mpr (div_pos hLog hMass).ne').symm

end
end Masullo
