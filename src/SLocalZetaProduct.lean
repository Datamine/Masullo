import SLocalFiniteZeta
import SLocalZetaUnfolding
import ArchimedeanProductZeta
import ArchimedeanMultiplicativeHaar

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev ArchTests := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FiniteCoordinates := ∀ v : S, v.val.adicCompletion F
private abbrev FiniteTests := locallyConstantTests (FiniteCoordinates F S)
private abbrev FiniteUnits := ∀ v : S, (v.val.adicCompletion F)ˣ
private abbrev Phases := ∀ v : S, (v.val.adicCompletion F)ˣ →ₜ* Circle


private abbrev ArchUnits := (InfiniteAdeleRing F)ˣ
private abbrev SIdeles := (SAdeles F S)ˣ
private abbrev NormOne := SLocalThetaNormOne F S
private abbrev SClasses := SIdeleQuotient F S

/-- The actual S-ideles split topologically and multiplicatively into their
archimedean part and the finitely many selected local unit groups. -/
def sLocalZetaIdeleCoordinates :
    SIdeles F S ≃ₜ* ArchUnits F × FiniteUnits F S :=
  (show SIdeles F S ≃ₜ* ArchUnits F × (FiniteCoordinates F S)ˣ from
    { toMulEquiv := MulEquiv.prodUnits
      continuous_toFun := Homeomorph.prodUnits.continuous
      continuous_invFun := Homeomorph.prodUnits.symm.continuous }).trans
    (show ArchUnits F × (FiniteCoordinates F S)ˣ ≃ₜ* ArchUnits F × FiniteUnits F S from
      { toMulEquiv := MulEquiv.prodCongr (.refl _) ContinuousMulEquiv.piUnits.toMulEquiv
        continuous_toFun := (Homeomorph.prodCongr (.refl _) ContinuousMulEquiv.piUnits.toHomeomorph).continuous
        continuous_invFun :=
          (Homeomorph.prodCongr (.refl _) ContinuousMulEquiv.piUnits.toHomeomorph).symm.continuous })

def sLocalArchZetaInsert (a : ArchUnits F) : SIdeles F S :=
  (sLocalZetaIdeleCoordinates F S).symm (a, 1)

def sLocalFiniteZetaInsert (v : S) (u : (v.val.adicCompletion F)ˣ) : SIdeles F S :=
  (sLocalZetaIdeleCoordinates F S).symm (1, Pi.mulSingle v u)

private theorem sLocalZetaIdeleCoordinates_val (p : ArchUnits F × FiniteUnits F S) :
    ((sLocalZetaIdeleCoordinates F S).symm p).val = (p.1.val, fun v => (p.2 v).val) := rfl

/-- Each coordinate insertion is a factor of the S-idèle with those coordinates. -/
theorem sLocalZetaIdeleCoordinates_factor (p : ArchUnits F × FiniteUnits F S) :
    (sLocalZetaIdeleCoordinates F S).symm p =
      sLocalArchZetaInsert F S p.1 * ∏ v : S, sLocalFiniteZetaInsert F S v (p.2 v) := by
  apply (sLocalZetaIdeleCoordinates F S).injective
  simp only [map_mul, map_prod, sLocalArchZetaInsert, sLocalFiniteZetaInsert,
    ContinuousMulEquiv.apply_symm_apply]
  have he : (∏ v : S, ((1 : ArchUnits F), Pi.mulSingle v (p.2 v))) = (1, p.2) := by
    apply Prod.ext
    · change (MonoidHom.fst _ _) (∏ v : S, ((1 : ArchUnits F), Pi.mulSingle v (p.2 v))) = _
      rw [map_prod]
      exact Finset.prod_const_one
    · change (MonoidHom.snd _ _) (∏ v : S, ((1 : ArchUnits F), Pi.mulSingle v (p.2 v))) = _
      rw [map_prod]
      exact Finset.univ_prod_mulSingle p.2
  rw [he, Prod.mk_mul_mk, mul_one, one_mul]

/-- The actual modulus equals the product of the archimedean and finite moduli. -/
theorem sLocalZetaIdeleCoordinates_norm (p : ArchUnits F × FiniteUnits F S) :
    sLocalIdeleNorm F S ((sLocalZetaIdeleCoordinates F S).symm p) =
      (∏ w : InfinitePlace F, ‖p.1.val w‖ ^ w.mult) * ∏ v : S, ‖(p.2 v).val‖ := by
  let g := (sLocalZetaIdeleCoordinates F S).symm p
  let a := (sLocalEmbed F S g).val
  have hout (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ S) : ‖a.val.2 w‖ = 1 := by
    have hv := (ideleOrder_eq_zero_iff F a w).mp
      ((sIdeleBlock_mem_iff F S a).mp (sLocalEmbed F S g).property w hw)
    rw [FinitePlace.norm_def, hv]
    simp
  change (∏ w : InfinitePlace F, ‖a.val.1 w‖ ^ w.mult) *
      (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖a.val.2 w‖) = _
  have harch : a.val.1 = p.1.val :=
    (sLocalEmbed_arch F S g).trans (congrArg Prod.fst (sLocalZetaIdeleCoordinates_val F S p))
  have hfin (v : S) : a.val.2 v.val = (p.2 v).val :=
    (sLocalEmbed_finite F S g v).trans
      (congrArg (fun x : SAdeles F S => x.2 v) (sLocalZetaIdeleCoordinates_val F S p))
  rw [harch, finprod_eq_prod_of_mulSupport_subset _ (fun w hw => of_not_not (fun h => hw (hout w h)))]
  congr 1
  calc
    _ = ∏ v : S, ‖a.val.2 v.val‖ := Finset.prod_subtype S (fun _ => Iff.rfl) (fun w => ‖a.val.2 w‖)
    _ = _ := Finset.prod_congr rfl fun v _ => congrArg norm (hfin v)

theorem sLocalFiniteZetaInsert_norm (v : S) (u : (v.val.adicCompletion F)ˣ) :
    sLocalIdeleNorm F S (sLocalFiniteZetaInsert F S v u) = ‖u.val‖ := by
  rw [sLocalFiniteZetaInsert, sLocalZetaIdeleCoordinates_norm]
  have ho (w : InfinitePlace F) : (1 : InfiniteAdeleRing F) w = 1 := rfl
  simp only [Units.val_one, ho, norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [Finset.prod_eq_single v]
  · rw [Pi.mulSingle_eq_same]
  · intro w _ hw
    rw [Pi.mulSingle_eq_of_ne hw, Units.val_one, norm_one]
  · simp

private theorem sLocalZetaWeight_phaseNorm (ω : PontryaginDual (NormOne F S)) (q : SClasses F S) :
    ‖sLocalZetaWeight F S ω 0 q‖ = 1 := by
  simp [sLocalZetaWeight, Circle.norm_coe]

private theorem sLocalZetaWeight_phaseTwist (ω : PontryaginDual (NormOne F S)) (z : ℂ)
    (q : SClasses F S) :
    sLocalZetaWeight F S ω z q = sLocalZetaWeight F S ω 0 q *
      Complex.exp (z * (Real.log (sLocalClassModulus F S q) : ℂ)) := by
  unfold sLocalZetaWeight
  simp only [zero_mul, Complex.exp_zero, one_mul]
  exact mul_comm _ _

/-- The unitary finite-place restrictions on the component with norm-one
character `ω`. -/
def sLocalFiniteZetaPhases (ω : PontryaginDual (NormOne F S)) (v : S) :
    (v.val.adicCompletion F)ˣ →ₜ* Circle := by
  let Q : (v.val.adicCompletion F)ˣ → SClasses F S :=
    fun u => QuotientGroup.mk (sLocalFiniteZetaInsert F S v u)
  let h (u : (v.val.adicCompletion F)ˣ) := sLocalZetaWeight F S ω 0 (Q u)
  have hn (u : (v.val.adicCompletion F)ˣ) : ‖h u‖ = 1 := sLocalZetaWeight_phaseNorm F S ω _
  have hm (u w : (v.val.adicCompletion F)ˣ) : Q (u*w) = Q u * Q w := by
    simp only [Q, sLocalFiniteZetaInsert, ← QuotientGroup.mk_mul, ← map_mul, Prod.mk_mul_mk,
      mul_one, Pi.mulSingle_mul]
  refine
    { toFun := fun u => ⟨h u, mem_sphere_zero_iff_norm.mpr (hn u)⟩
      map_one' := ?_
      map_mul' := fun u w => Subtype.ext (by
        change sLocalZetaWeight F S ω 0 (Q (u*w)) = h u * h w
        rw [hm, sLocalZetaWeight_mul])
      continuous_toFun := ?_ }
  · apply Subtype.ext
    change h 1 = 1
    have he : h 1 = h 1 * h 1 := by
      have hd := sLocalZetaWeight_mul F S ω 0 (Q 1) (Q 1)
      rw [← hm, mul_one] at hd
      exact hd
    have hne : h 1 ≠ 0 := by
      intro hzero
      have hz := hn 1
      rw [hzero, norm_zero] at hz
      exact zero_ne_one hz
    exact mul_left_cancel₀ hne (by rw [← he, mul_one])
  · have hQ : Continuous Q := by
      apply QuotientGroup.continuous_mk.comp
      apply (sLocalZetaIdeleCoordinates F S).symm.continuous.comp
      apply continuous_const.prodMk
      exact continuous_pi fun w => by
        by_cases hw : w = v
        · subst w
          simp only [Pi.mulSingle_eq_same]
          exact continuous_id
        · simpa only [Pi.mulSingle_eq_of_ne hw] using
            (continuous_const : Continuous (fun _ : (v.val.adicCompletion F)ˣ =>
              (1 : (w.val.adicCompletion F)ˣ)))
    exact ((sLocalZetaWeight_continuous F S ω 0).comp hQ).subtype_mk _

/-- On the actual S-ideles, the spectral weight is the archimedean weight
times the product of the twisted finite-place restrictions. -/
theorem sLocalZetaWeight_product (ω : PontryaginDual (NormOne F S)) (z : ℂ)
    (p : ArchUnits F × FiniteUnits F S) :
    sLocalZetaWeight F S ω z (QuotientGroup.mk ((sLocalZetaIdeleCoordinates F S).symm p)) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S p.1)) *
        ∏ v : S, ((sLocalFiniteZetaPhases F S ω v (p.2 v) : ℂ) *
          finiteZetaWeight F v.val z (p.2 v)) := by
  let i : SIdeles F S →* ℂ :=
    { toFun := fun u => sLocalZetaWeight F S ω z (QuotientGroup.mk u)
      map_one' := by
        have hd := sLocalZetaWeight_mul F S ω z (1 : SClasses F S) 1
        have hone : (1 : SIdeleQuotient F S) * 1 = 1 := mul_one (1 : SIdeleQuotient F S)
        rw [hone] at hd
        have hne : sLocalZetaWeight F S ω z (1 : SClasses F S) ≠ 0 := by
          unfold sLocalZetaWeight
          exact mul_ne_zero (Complex.exp_ne_zero _) (Circle.coe_ne_zero _)
        change sLocalZetaWeight F S ω z (QuotientGroup.mk (1 : SIdeles F S)) = 1
        rw [QuotientGroup.mk_one]
        exact mul_left_cancel₀ hne (by rw [← hd, mul_one])
      map_mul' := fun u w => by
        change sLocalZetaWeight F S ω z (QuotientGroup.mk (u*w)) =
          sLocalZetaWeight F S ω z (QuotientGroup.mk u) * sLocalZetaWeight F S ω z (QuotientGroup.mk w)
        rw [QuotientGroup.mk_mul, sLocalZetaWeight_mul] }
  change i ((sLocalZetaIdeleCoordinates F S).symm p) = _
  rw [sLocalZetaIdeleCoordinates_factor F S p, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  change sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalFiniteZetaInsert F S v (p.2 v))) = _
  rw [sLocalZetaWeight_phaseTwist, sLocalClassModulus_mk, sLocalFiniteZetaInsert_norm]
  rfl

private abbrev ZetaRealPlaces := {w : InfinitePlace F // w.IsReal}
private abbrev ZetaComplexPlaces := {w : InfinitePlace F // w.IsComplex}

private theorem sLocalArchZetaInsert_norm (a : ArchUnits F) :
    sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) = ‖a.val‖ := by
  rw [sLocalArchZetaInsert, sLocalZetaIdeleCoordinates_norm, InfiniteAdeleRing.norm_def]
  simp

private def sLocalArchUnitaryWeight (ω : PontryaginDual (NormOne F S)) : ArchUnits F →ₜ* ℂ := by
  let Q (a : ArchUnits F) : SClasses F S := QuotientGroup.mk (sLocalArchZetaInsert F S a)
  have hQ (a b : ArchUnits F) : Q (a * b) = Q a * Q b := by
    simp only [Q, sLocalArchZetaInsert, ← QuotientGroup.mk_mul, ← map_mul, Prod.mk_mul_mk, mul_one]
  refine
    { toFun := fun a => sLocalZetaWeight F S ω 0 (Q a)
      map_one' := ?_
      map_mul' := fun a b => by rw [hQ, sLocalZetaWeight_mul]
      continuous_toFun := (sLocalZetaWeight_continuous F S ω 0).comp
        (QuotientGroup.continuous_mk.comp ((sLocalZetaIdeleCoordinates F S).symm.continuous.comp
          (continuous_id.prodMk continuous_const))) }
  have h := sLocalZetaWeight_mul F S ω 0 (Q 1) (Q 1)
  rw [← hQ, mul_one] at h
  change sLocalZetaWeight F S ω 0 (Q 1) = 1
  have hne := norm_ne_zero_iff.mp ((sLocalZetaWeight_phaseNorm F S ω (Q 1)).trans_ne one_ne_zero)
  exact mul_left_cancel₀ hne (by rw [← h, mul_one])

private def sLocalArchUnitaryCoordinates (ω : PontryaginDual (NormOne F S)) :
    ((ZetaRealPlaces F → ℝˣ) × (ZetaComplexPlaces F → ℂˣ)) →ₜ* ℂ :=
  (sLocalArchUnitaryWeight F S ω).comp (ContinuousMonoidHom.toContinuousMonoidHom (infiniteAdeleUnitsCoordinates F).symm)

private def realArchCoordinateInsert (v : ZetaRealPlaces F) :
    ℝˣ →ₜ* ((ZetaRealPlaces F → ℝˣ) × (ZetaComplexPlaces F → ℂˣ)) where
  toFun x := (Pi.mulSingle v x, 1)
  map_one' := by simp
  map_mul' x y := by simp [Pi.mulSingle_mul]
  continuous_toFun := (continuous_mulSingle (A := fun _ : ZetaRealPlaces F => ℝˣ) v).prodMk continuous_const

private def complexArchCoordinateInsert (v : ZetaComplexPlaces F) :
    ℂˣ →ₜ* ((ZetaRealPlaces F → ℝˣ) × (ZetaComplexPlaces F → ℂˣ)) where
  toFun x := (1, Pi.mulSingle v x)
  map_one' := by simp
  map_mul' x y := by simp [Pi.mulSingle_mul]
  continuous_toFun := continuous_const.prodMk (continuous_mulSingle (A := fun _ : ZetaComplexPlaces F => ℂˣ) v)

private def sLocalRealArchCharacter (ω : PontryaginDual (NormOne F S)) (v : ZetaRealPlaces F) :
    ℝˣ →ₜ* ℂ :=
  (sLocalArchUnitaryCoordinates F S ω).comp (realArchCoordinateInsert F v)

private def sLocalComplexArchCharacter (ω : PontryaginDual (NormOne F S)) (v : ZetaComplexPlaces F) :
    ℂˣ →ₜ* ℂ :=
  (sLocalArchUnitaryCoordinates F S ω).comp (complexArchCoordinateInsert F v)

private theorem sLocalRealArchCharacter_classification (ω : PontryaginDual (NormOne F S))
    (v : ZetaRealPlaces F) :
    ∃ p : ℂ × ℕ, p.1.re = 0 ∧ ∀ u : ℝˣ,
      sLocalRealArchCharacter F S ω v u =
        (‖(u : ℝ)‖ : ℂ) ^ p.1 * (if (u : ℝ) < 0 then (-1 : ℂ) ^ p.2 else 1) := by
  have hnorm (u : ℝˣ) : ‖sLocalRealArchCharacter F S ω v u‖ = 1 :=
    sLocalZetaWeight_phaseNorm F S ω _
  obtain ⟨p, hp, _⟩ := existsUnique_realUnits_character_parameters (sLocalRealArchCharacter F S ω v) hnorm
  refine ⟨(p.1, p.2.val), hp.1, fun u => ?_⟩
  rw [hp.2]
  rcases lt_or_gt_of_ne (Units.ne_zero u) with h | h
  · simp [h, not_lt_of_ge h.le]
  · simp [h, not_lt_of_ge h.le]

private theorem sLocalComplexArchCharacter_classification (ω : PontryaginDual (NormOne F S))
    (v : ZetaComplexPlaces F) :
    ∃ p : ℂ × ℤ, p.1.re = 0 ∧ ∀ u : ℂˣ,
      sLocalComplexArchCharacter F S ω v u =
        ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ p.1 * ((u : ℂ) / (‖(u : ℂ)‖ : ℂ)) ^ p.2 :=
  (existsUnique_complexUnits_character_parameters (sLocalComplexArchCharacter F S ω v)
    (fun _ => sLocalZetaWeight_phaseNorm F S ω _)).exists

/-- Place-dependent imaginary shifts and sign parities of the unitary
part of the S-local archimedean weight. -/
def sLocalRealArchParameters (ω : PontryaginDual (NormOne F S)) (v : ZetaRealPlaces F) :
    ℂ × ℕ := (sLocalRealArchCharacter_classification F S ω v).choose

/-- Place-dependent imaginary shifts and angular powers of the unitary
part of the S-local archimedean weight. -/
def sLocalComplexArchParameters (ω : PontryaginDual (NormOne F S)) (v : ZetaComplexPlaces F) :
    ℂ × ℤ := (sLocalComplexArchCharacter_classification F S ω v).choose

theorem sLocalRealArchParameters_re (ω : PontryaginDual (NormOne F S)) (v : ZetaRealPlaces F) :
    (sLocalRealArchParameters F S ω v).1.re = 0 :=
  (sLocalRealArchCharacter_classification F S ω v).choose_spec.1

theorem sLocalComplexArchParameters_re (ω : PontryaginDual (NormOne F S)) (v : ZetaComplexPlaces F) :
    (sLocalComplexArchParameters F S ω v).1.re = 0 :=
  (sLocalComplexArchCharacter_classification F S ω v).choose_spec.1

/-- Inverting the norm-one character inverts the unitary local weight. -/
theorem sLocalZetaUnitaryWeight_inv (ω : PontryaginDual (NormOne F S)) (q : SClasses F S) :
    sLocalZetaWeight F S ω⁻¹ 0 q = (sLocalZetaWeight F S ω 0 q)⁻¹ := by
  simp only [sLocalZetaWeight, zero_mul, Complex.exp_zero, one_mul]
  exact Circle.coe_inv _

/-- Reflection inverts the actual finite-place phase on each coordinate. -/
theorem sLocalFiniteZetaPhases_inv (ω : PontryaginDual (NormOne F S)) (v : S) :
    sLocalFiniteZetaPhases F S ω⁻¹ v = (sLocalFiniteZetaPhases F S ω v)⁻¹ := by
  ext u
  exact sLocalZetaUnitaryWeight_inv F S ω _

/-- Reflection negates the real radial shift and leaves the sign parity. -/
theorem sLocalRealArchParameters_inv (ω : PontryaginDual (NormOne F S)) (v : ZetaRealPlaces F) :
    (sLocalRealArchParameters F S ω⁻¹ v).1 = -(sLocalRealArchParameters F S ω v).1 ∧
      (sLocalRealArchParameters F S ω⁻¹ v).2 % 2 = (sLocalRealArchParameters F S ω v).2 % 2 := by
  let a := sLocalRealArchParameters F S ω v
  let b := sLocalRealArchParameters F S ω⁻¹ v
  let a' : ℂ × Fin 2 := (-a.1, ⟨a.2 % 2, Nat.mod_lt _ (by norm_num)⟩)
  let b' : ℂ × Fin 2 := (b.1, ⟨b.2 % 2, Nat.mod_lt _ (by norm_num)⟩)
  let c := sLocalRealArchCharacter F S ω⁻¹ v
  obtain ⟨p, _, hp⟩ := existsUnique_realUnits_character_parameters c
    (fun _ ↦ sLocalZetaWeight_phaseNorm F S ω⁻¹ _)
  have hsign (u : ℝˣ) (n : ℕ) :
      (if (u : ℝ) < 0 then (-1 : ℂ) ^ n else 1) =
        (if 0 < (u : ℝ) then (1 : ℂ) else -1) ^ (n % 2) := by
    rcases lt_or_gt_of_ne u.ne_zero with hn | hp
    · rw [ite_eq_left hn, ite_eq_right (not_lt.mpr hn.le)]
      exact neg_one_pow_eq_pow_mod_two n
    · simp [not_lt.mpr hp.le, hp]
  have ha : a' = p := by
    apply hp
    refine ⟨by simp [a', a, sLocalRealArchParameters_re], fun u ↦ ?_⟩
    have h : c u = (sLocalRealArchCharacter F S ω v u)⁻¹ :=
      sLocalZetaUnitaryWeight_inv F S ω _
    have h₀ (u : ℝˣ) : (if 0 < (u : ℝ) then (1 : ℂ) else -1)⁻¹ =
        (if 0 < (u : ℝ) then (1 : ℂ) else -1) := by
      split <;> simp
    rw [h, (sLocalRealArchCharacter_classification F S ω v).choose_spec.2 u, hsign,
      mul_inv, ← Complex.cpow_neg, ← inv_pow, h₀]
    rfl
  have hb : b' = p := hp b' ⟨sLocalRealArchParameters_re F S ω⁻¹ v, fun u ↦
    ((sLocalRealArchCharacter_classification F S ω⁻¹ v).choose_spec.2 u).trans
      (congrArg (fun r : ℂ ↦ ((‖(u : ℝ)‖ : ℝ) : ℂ) ^ b.1 * r) (hsign u b.2))⟩
  have he := hb.trans ha.symm
  exact ⟨congrArg Prod.fst he, congrArg (fun q : ℂ × Fin 2 ↦ q.2.val) he⟩

/-- Reflection negates both the complex radial shift and the angular index. -/
theorem sLocalComplexArchParameters_inv (ω : PontryaginDual (NormOne F S)) (v : ZetaComplexPlaces F) :
    sLocalComplexArchParameters F S ω⁻¹ v =
      (-(sLocalComplexArchParameters F S ω v).1, -(sLocalComplexArchParameters F S ω v).2) := by
  let a := sLocalComplexArchParameters F S ω v
  let c := sLocalComplexArchCharacter F S ω⁻¹ v
  obtain ⟨p, _, hp⟩ := existsUnique_complexUnits_character_parameters c
    (fun _ ↦ sLocalZetaWeight_phaseNorm F S ω⁻¹ _)
  have hb : sLocalComplexArchParameters F S ω⁻¹ v = p :=
    hp _ (sLocalComplexArchCharacter_classification F S ω⁻¹ v).choose_spec
  have ha : (-a.1, -a.2) = p := by
    apply hp
    refine ⟨by simp [a, sLocalComplexArchParameters_re], fun u ↦ ?_⟩
    have h : c u = (sLocalComplexArchCharacter F S ω v u)⁻¹ :=
      sLocalZetaUnitaryWeight_inv F S ω _
    rw [h, (sLocalComplexArchCharacter_classification F S ω v).choose_spec.2 u,
      mul_inv, ← Complex.cpow_neg, ← zpow_neg]
    rfl
  exact hb.trans ha.symm

/-- The trivial real character has zero shift and even parity. -/
theorem sLocalRealArchParameters_one (v : ZetaRealPlaces F) :
    (sLocalRealArchParameters F S 1 v).1 = 0 ∧
      (sLocalRealArchParameters F S 1 v).2 % 2 = 0 := by
  have hshift := (sLocalRealArchParameters_inv F S 1 v).1
  rw [inv_one] at hshift
  refine ⟨by linear_combination hshift / 2, ?_⟩
  have hunit : sLocalRealArchCharacter F S 1 v (-1) = 1 := by
    change sLocalZetaWeight F S 1 0 _ = 1
    simp [sLocalZetaWeight]
  have hparity := (sLocalRealArchCharacter_classification F S 1 v).choose_spec.2 (-1)
  rw [hunit] at hparity
  have he : (-1 : ℂ) ^ (sLocalRealArchParameters F S 1 v).2 = 1 := by
    simpa [sLocalRealArchParameters] using hparity.symm
  exact Nat.even_iff.mp ((neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp he)

/-- The trivial complex character has zero shift and angular index zero. -/
theorem sLocalComplexArchParameters_one (v : ZetaComplexPlaces F) :
    sLocalComplexArchParameters F S 1 v = (0, 0) := by
  have h := sLocalComplexArchParameters_inv F S 1 v
  rw [inv_one] at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext (by linear_combination h₁ / 2) (by omega)

/-- The restricted archimedean character determines the radial and angular
parameters, with the real sign exponent determined modulo two. -/
theorem sLocalArchParameters_eq_of_weight {T : Finset (HeightOneSpectrum (𝓞 F))}
    (ω : PontryaginDual (NormOne F S)) (τ : PontryaginDual (NormOne F T))
    (h : ∀ a : ArchUnits F,
      sLocalZetaWeight F S ω 0 (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
        sLocalZetaWeight F T τ 0 (QuotientGroup.mk (sLocalArchZetaInsert F T a))) :
    (∀ v : ZetaRealPlaces F,
      (sLocalRealArchParameters F S ω v).1 = (sLocalRealArchParameters F T τ v).1 ∧
      (sLocalRealArchParameters F S ω v).2 % 2 = (sLocalRealArchParameters F T τ v).2 % 2) ∧
    (∀ v : ZetaComplexPlaces F, sLocalComplexArchParameters F S ω v = sLocalComplexArchParameters F T τ v) := by
  constructor
  · intro v
    let a := sLocalRealArchParameters F S ω v
    let b := sLocalRealArchParameters F T τ v
    let a' : ℂ × Fin 2 := (a.1, ⟨a.2 % 2, Nat.mod_lt _ (by norm_num)⟩)
    let b' : ℂ × Fin 2 := (b.1, ⟨b.2 % 2, Nat.mod_lt _ (by norm_num)⟩)
    let c := sLocalRealArchCharacter F S ω v
    have hc (u : ℝˣ) : c u = sLocalRealArchCharacter F T τ v u :=
      h ((infiniteAdeleUnitsCoordinates F).symm (realArchCoordinateInsert F v u))
    obtain ⟨p, _, hp⟩ := existsUnique_realUnits_character_parameters c (fun _ ↦ sLocalZetaWeight_phaseNorm F S ω _)
    have hS (u : ℝˣ) := (sLocalRealArchCharacter_classification F S ω v).choose_spec.2 u
    have hT (u : ℝˣ) := (sLocalRealArchCharacter_classification F T τ v).choose_spec.2 u
    have hsign (u : ℝˣ) (n : ℕ) :
        (if (u : ℝ) < 0 then (-1 : ℂ) ^ n else 1) =
          (if 0 < (u : ℝ) then (1 : ℂ) else -1) ^ (n % 2) := by
      rcases lt_or_gt_of_ne (Units.ne_zero u) with hn | hp
      · rw [ite_eq_left hn, ite_eq_right (not_lt.mpr hn.le)]
        exact neg_one_pow_eq_pow_mod_two n
      · simp [not_lt.mpr hp.le, hp]
    have ha : a' = p := hp a' ⟨sLocalRealArchParameters_re F S ω v, fun u ↦
      (hS u).trans (congrArg (fun r : ℂ ↦ ((‖(u : ℝ)‖ : ℝ) : ℂ) ^ a.1 * r) (hsign u a.2))⟩
    have hb : b' = p := hp b' ⟨sLocalRealArchParameters_re F T τ v, fun u ↦
      ((hc u).trans (hT u)).trans
        (congrArg (fun r : ℂ ↦ ((‖(u : ℝ)‖ : ℝ) : ℂ) ^ b.1 * r) (hsign u b.2))⟩
    have he := ha.trans hb.symm
    have he₁ : a.1 = b.1 := congrArg (fun p : ℂ × Fin 2 ↦ p.1) he
    have he₂ : a.2 % 2 = b.2 % 2 := congrArg (fun p : ℂ × Fin 2 ↦ p.2.val) he
    exact ⟨he₁, he₂⟩
  · intro v
    let a := sLocalComplexArchParameters F S ω v
    let b := sLocalComplexArchParameters F T τ v
    let c := sLocalComplexArchCharacter F S ω v
    have hc (u : ℂˣ) : c u = sLocalComplexArchCharacter F T τ v u :=
      h ((infiniteAdeleUnitsCoordinates F).symm (complexArchCoordinateInsert F v u))
    obtain ⟨p, _, hp⟩ := existsUnique_complexUnits_character_parameters c
      (fun _ ↦ sLocalZetaWeight_phaseNorm F S ω _)
    have ha : a = p := hp a (sLocalComplexArchCharacter_classification F S ω v).choose_spec
    have hb : b = p := hp b ⟨sLocalComplexArchParameters_re F T τ v, fun u ↦
      (hc u).trans ((sLocalComplexArchCharacter_classification F T τ v).choose_spec.2 u)⟩
    exact ha.trans hb.symm

/-- Equality of the restricted archimedean characters gives equality
of the Gamma denominators. The real sign exponent is determined modulo two. -/
theorem sLocalArchZetaDenominators_eq_of_weight {T : Finset (HeightOneSpectrum (𝓞 F))}
    (ω : PontryaginDual (NormOne F S)) (τ : PontryaginDual (NormOne F T))
    (h : ∀ a : ArchUnits F,
      sLocalZetaWeight F S ω 0 (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
        sLocalZetaWeight F T τ 0 (QuotientGroup.mk (sLocalArchZetaInsert F T a))) :
    (∀ (v : ZetaRealPlaces F) (z : ℂ),
      realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
        (z + (sLocalRealArchParameters F S ω v).1) =
      realArchZetaDenominator (sLocalRealArchParameters F T τ v).2
        (z + (sLocalRealArchParameters F T τ v).1)) ∧
    (∀ (v : ZetaComplexPlaces F) (z : ℂ),
      complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
        (z + (sLocalComplexArchParameters F S ω v).1) =
      complexArchZetaDenominator (sLocalComplexArchParameters F T τ v).2
        (z + (sLocalComplexArchParameters F T τ v).1)) := by
  obtain ⟨hR, hC⟩ := sLocalArchParameters_eq_of_weight F S ω τ h
  constructor
  · intro v z
    obtain ⟨he₁, he₂⟩ := hR v
    rw [realArchZetaDenominator, realArchZetaDenominator, he₁, he₂]
  · intro v z
    rw [hC v]

private theorem sLocalArchUnitaryCoordinates_factor (ω : PontryaginDual (NormOne F S))
    (p : (ZetaRealPlaces F → ℝˣ) × (ZetaComplexPlaces F → ℂˣ)) :
    sLocalArchUnitaryCoordinates F S ω p =
      (∏ v : ZetaRealPlaces F, sLocalRealArchCharacter F S ω v (p.1 v)) *
      ∏ v : ZetaComplexPlaces F, sLocalComplexArchCharacter F S ω v (p.2 v) := by
  have hR : (∏ v : ZetaRealPlaces F, realArchCoordinateInsert F v (p.1 v)) = (p.1, 1) := by
    apply Prod.ext
    · change (MonoidHom.fst _ _) (∏ v : ZetaRealPlaces F, realArchCoordinateInsert F v (p.1 v)) = _
      rw [map_prod]
      change (∏ v : ZetaRealPlaces F, Pi.mulSingle v (p.1 v)) = p.1
      exact Finset.univ_prod_mulSingle p.1
    · change (MonoidHom.snd _ _) (∏ v : ZetaRealPlaces F, realArchCoordinateInsert F v (p.1 v)) = _
      rw [map_prod]
      change (∏ _ : ZetaRealPlaces F, (1 : ZetaComplexPlaces F → ℂˣ)) = 1
      exact Finset.prod_const_one
  have hC : (∏ v : ZetaComplexPlaces F, complexArchCoordinateInsert F v (p.2 v)) = (1, p.2) := by
    apply Prod.ext
    · change (MonoidHom.fst _ _) (∏ v : ZetaComplexPlaces F, complexArchCoordinateInsert F v (p.2 v)) = _
      rw [map_prod]
      change (∏ _ : ZetaComplexPlaces F, (1 : ZetaRealPlaces F → ℝˣ)) = 1
      exact Finset.prod_const_one
    · change (MonoidHom.snd _ _) (∏ v : ZetaComplexPlaces F, complexArchCoordinateInsert F v (p.2 v)) = _
      rw [map_prod]
      change (∏ v : ZetaComplexPlaces F, Pi.mulSingle v (p.2 v)) = p.2
      exact Finset.univ_prod_mulSingle p.2
  have hp : (p.1, (1 : ZetaComplexPlaces F → ℂˣ)) * ((1 : ZetaRealPlaces F → ℝˣ), p.2) = p := by
    simp
  calc
    _ = sLocalArchUnitaryCoordinates F S ω
        ((∏ v : ZetaRealPlaces F, realArchCoordinateInsert F v (p.1 v)) *
          ∏ v : ZetaComplexPlaces F, complexArchCoordinateInsert F v (p.2 v)) := by
      rw [hR, hC, hp]
    _ = _ := by rw [map_mul, map_prod, map_prod]; rfl

private theorem cpow_real_prod {ι : Type*} (T : Finset ι) (r : ι → ℝ) (z : ℂ)
    (hr : ∀ i, 0 ≤ r i) :
    ((∏ i ∈ T, r i : ℝ) : ℂ) ^ z = ∏ i ∈ T, ((r i : ℝ) : ℂ) ^ z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr i) (Finset.prod_nonneg fun j _ => hr j), ih]

private theorem cpow_real_eq_exp_log {t : ℝ} (ht : 0 < t) (s : ℂ) :
    (t : ℂ) ^ s = Complex.exp (s * (Real.log t : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ← Complex.ofReal_log ht.le, mul_comm]

private theorem sLocalArchZetaTwist_eq_product (a : ArchUnits F) (z : ℂ) :
    let p := infiniteAdeleUnitsCoordinates F a
    Complex.exp (z * (Real.log (sLocalIdeleNorm F S (sLocalArchZetaInsert F S a)) : ℂ)) =
      (∏ v : ZetaRealPlaces F, (‖((p.1 v : ℝˣ) : ℝ)‖ : ℂ) ^ z) *
        ∏ v : ZetaComplexPlaces F, ((‖((p.2 v : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z := by
  dsimp only
  let p := infiniteAdeleUnitsCoordinates F a
  let r (v : ZetaRealPlaces F) := ‖((p.1 v : ℝˣ) : ℝ)‖
  let t (v : ZetaComplexPlaces F) := ‖((p.2 v : ℂˣ) : ℂ)‖ ^ 2
  have hr (v : ZetaRealPlaces F) : 0 < r v := norm_pos_iff.mpr (Units.ne_zero _)
  have ht (v : ZetaComplexPlaces F) : 0 < t v := pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) _
  have hn : sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) =
      (∏ v : ZetaRealPlaces F, r v) * ∏ v : ZetaComplexPlaces F, t v := by
    rw [sLocalArchZetaInsert_norm, ← archModulus_of_infiniteAdele]
    rfl
  change _ = (∏ v, (r v : ℂ) ^ z) * ∏ v, (t v : ℂ) ^ z
  rw [hn, ← cpow_real_eq_exp_log (mul_pos (Finset.prod_pos fun v _ => hr v)
      (Finset.prod_pos fun v _ => ht v)),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      (Finset.prod_nonneg fun v _ => (hr v).le) (Finset.prod_nonneg fun v _ => (ht v).le),
    cpow_real_prod _ _ _ (fun v => (hr v).le), cpow_real_prod _ _ _ (fun v => (ht v).le)]

/-- The real local factor of the archimedean S-idelic weight. -/
def sLocalRealArchWeight (ω : PontryaginDual (NormOne F S)) (v : ZetaRealPlaces F)
    (z : ℂ) (u : ℝˣ) : ℂ :=
  (‖(u : ℝ)‖ : ℂ) ^ (z + (sLocalRealArchParameters F S ω v).1) *
    (if (u : ℝ) < 0 then (-1 : ℂ) ^ (sLocalRealArchParameters F S ω v).2 else 1)

/-- The complex local factor of the archimedean S-idelic weight. -/
def sLocalComplexArchWeight (ω : PontryaginDual (NormOne F S)) (v : ZetaComplexPlaces F)
    (z : ℂ) (u : ℂˣ) : ℂ :=
  ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z + (sLocalComplexArchParameters F S ω v).1) *
    ((u : ℂ) / (‖(u : ℂ)‖ : ℂ)) ^ (sLocalComplexArchParameters F S ω v).2

/-- On the real and complex coordinate groups the actual archimedean
S-idelic weight is a product of the shifted local characters. -/
theorem sLocalArchZetaWeight_eq_product (ω : PontryaginDual (NormOne F S))
    (z : ℂ) (a : ArchUnits F) :
    let p := infiniteAdeleUnitsCoordinates F a
    sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
      (∏ v : ZetaRealPlaces F, sLocalRealArchWeight F S ω v z (p.1 v)) *
        ∏ v : ZetaComplexPlaces F, sLocalComplexArchWeight F S ω v z (p.2 v) := by
  dsimp only
  let p := infiniteAdeleUnitsCoordinates F a
  have hp : sLocalZetaWeight F S ω 0 (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
      sLocalArchUnitaryCoordinates F S ω p := by
    change _ = sLocalArchUnitaryWeight F S ω ((infiniteAdeleUnitsCoordinates F).symm p)
    rw [show p = infiniteAdeleUnitsCoordinates F a from rfl, ContinuousMulEquiv.symm_apply_apply]
    rfl
  rw [sLocalZetaWeight_phaseTwist, sLocalClassModulus_mk, hp,
    sLocalArchUnitaryCoordinates_factor, sLocalArchZetaTwist_eq_product]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [(sLocalRealArchCharacter_classification F S ω v).choose_spec.2]
    have hne : (‖((p.1 v : ℝˣ) : ℝ)‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero _))
    rw [sLocalRealArchWeight, Complex.cpow_add _ _ hne]
    unfold sLocalRealArchParameters
    ring
  · apply Finset.prod_congr rfl
    intro v _
    rw [(sLocalComplexArchCharacter_classification F S ω v).choose_spec.2]
    have hne : ((‖((p.2 v : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (Units.ne_zero _)))
    rw [sLocalComplexArchWeight, Complex.cpow_add _ _ hne]
    unfold sLocalComplexArchParameters
    ring

/-- Contract the finite factor of an arbitrary S-local test with a finite
distribution. The output is a joint archimedean Schwartz test. -/
def sLocalBruhatContractFinite (l : FiniteTests F S →ₗ[ℂ] ℂ) :
    sLocalBruhatImage F S →L[ℂ] ArchTests F := by
  let A := ArchTests F
  let B := FiniteTests F S
  letI : PolynormableSpace ℂ A := (schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).toPolynormableSpace
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  let T : A →ₗ[ℂ] B →ₗ[ℂ] A :=
    { toFun := fun φ =>
        { toFun := fun ψ => l ψ • φ
          map_add' := fun ψ τ => by rw [map_add, add_smul]
          map_smul' := fun a ψ => by rw [map_smul, smul_eq_mul, mul_smul]; rfl }
      map_add' := fun φ γ => LinearMap.ext fun ψ => smul_add _ _ _
      map_smul' := fun a φ => LinearMap.ext fun ψ => smul_comm _ _ _ }
  let e := sLocalBruhatTensorEquiv F S
  have hT : Continuous (TensorProduct.lift T : A ⊗[ℂ] B → A) := by
    apply (continuous_inductiveTensor_lift_iff T).mpr
    constructor
    · intro ψ
      exact continuous_const_smul (l ψ)
    · intro φ
      exact finest_linear_continuous (T φ)
  exact (⟨TensorProduct.lift T, hT⟩ : (A ⊗[ℂ] B) →L[ℂ] A).comp e.symm.toContinuousLinearMap

@[simp] theorem sLocalBruhatContractFinite_pure (l : FiniteTests F S →ₗ[ℂ] ℂ)
    (φ : ArchTests F) (ψ : FiniteTests F S) :
    sLocalBruhatContractFinite F S l (sLocalBruhatPure F S φ ψ) = l ψ • φ := by
  let A := ArchTests F
  let B := FiniteTests F S
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  let e := sLocalBruhatTensorEquiv F S
  have he : e (φ ⊗ₜ[ℂ] ψ) = sLocalBruhatPure F S φ ψ :=
    TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) φ ψ
  rw [← he]
  unfold sLocalBruhatContractFinite
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_mk',
    TensorProduct.lift.tmul]
  rfl

theorem sLocalBruhatPure_span :
    Submodule.span ℂ {f : sLocalBruhatImage F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = f} = ⊤ := by
  let A := ArchTests F
  let B := FiniteTests F S
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  let e := sLocalBruhatTensorEquiv F S
  apply Submodule.eq_top_iff'.mpr
  intro f
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul φ ψ => exact Submodule.subset_span ⟨φ, ψ, (TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) φ ψ).symm⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Evaluate a finite slice while keeping all archimedean variables. -/
def sLocalBruhatFiniteSlice (x : FiniteCoordinates F S) :
    sLocalBruhatImage F S →L[ℂ] ArchTests F :=
  sLocalBruhatContractFinite F S
    { toFun := fun ψ => ψ.val x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem sLocalBruhatFiniteSlice_apply (f : sLocalBruhatImage F S)
    (x : FiniteCoordinates F S) (a : InfiniteAdeleRing F) :
    sLocalBruhatFiniteSlice F S x f (InfiniteAdeleRing.ringEquiv_mixedSpace F a) =
      sLocalBruhatRestriction F S f.val (a, x) := by
  have hf : f ∈ Submodule.span ℂ {g : sLocalBruhatImage F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  let e (g : sLocalBruhatImage F S) : ℂ :=
    sLocalBruhatFiniteSlice F S x g (InfiniteAdeleRing.ringEquiv_mixedSpace F a)
  let d (g : sLocalBruhatImage F S) : ℂ := sLocalBruhatRestriction F S g.val (a, x)
  change e f = d f
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, ψ, rfl⟩ := hg
    dsimp [e, d, sLocalBruhatFiniteSlice]
    rw [sLocalBruhatContractFinite_pure, sLocalBruhatPure_restrict]
    change ψ.val x * φ _ = _
    exact mul_comm _ _
  | zero => simp [e, d, sLocalBruhatRestriction]
  | add f g _ _ hf hg =>
    have h₁ : e (f + g) = e f + e g := by simp [e]
    have h₂ : d (f + g) = d f + d g := by rfl
    rw [h₁, h₂, hf, hg]
  | smul c f _ hf =>
    have h₁ : e (c • f) = c * e f := by
      change sLocalBruhatFiniteSlice F S x (c • f) _ = _
      rw [map_smul]
      rfl
    have h₂ : d (c • f) = c * d f := by rfl
    rw [h₁, h₂, hf]

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
variable (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ) [∀ v : S, (μ v).IsHaarMeasure]
  [∀ v : S, SigmaFinite (μ v)]

/-- Partially continue the S-local zeta distribution in the finite-place
spectral parameter while retaining the joint archimedean test. -/
def sLocalFiniteZetaSchwartzTest (χ : Phases F S) (z : ℂ) :
    sLocalBruhatImage F S →L[ℂ] ArchTests F := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  exact sLocalBruhatContractFinite F S (sLocalFiniteZetaContinued F S μ χ z).toLinearMap

/-- Pairing the continued finite contraction with any archimedean tempered
distribution gives a meromorphic function for every S-local test. -/
theorem sLocalFiniteZetaSchwartzTest_meromorphic (χ : Phases F S)
    (L : ℂ → ArchTests F →L[ℂ] ℂ)
    (hL : ∀ φ, Meromorphic (fun z => L z φ)) (f : sLocalBruhatImage F S) :
    Meromorphic (fun z => L z (sLocalFiniteZetaSchwartzTest F S μ χ z f)) := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  have hf : f ∈ Submodule.span ℂ {g : sLocalBruhatImage F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, ψ, rfl⟩ := hg
    have he : (fun z => L z (sLocalFiniteZetaSchwartzTest F S μ χ z
        (sLocalBruhatPure F S φ ψ))) =
        fun z => sLocalFiniteZetaContinued F S μ χ z ψ * L z φ := by
      funext z
      rw [sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure, map_smul]
      rfl
    rw [he]
    exact (sLocalFiniteZetaContinued_meromorphic F S μ χ ψ).mul (hL φ)
  | zero =>
    simpa only [map_zero] using (show Meromorphic (fun _ : ℂ => (0 : ℂ)) from fun z => MeromorphicAt.const _ z)
  | add f g _ _ hf hg =>
    simp only [map_add]
    exact hf.add hg
  | smul c f _ hf =>
    have he : (fun z => L z (sLocalFiniteZetaSchwartzTest F S μ χ z (c • f))) =
        fun z => c * L z (sLocalFiniteZetaSchwartzTest F S μ χ z f) := by
      funext z
      rw [map_smul, map_smul]
      rfl
    rw [he]
    exact (show Meromorphic (fun _ : ℂ => c) from fun z => MeromorphicAt.const _ z).mul hf

/-- On the initial half-plane, pairing after the finite contraction equals
integration of the actual finite slices against the product of local weights. -/
theorem sLocalFiniteZetaSchwartzTest_eq_integral (χ : Phases F S)
    (L : ArchTests F →L[ℂ] ℂ) (f : sLocalBruhatImage F S) (z : ℂ) (hz : 0 < z.re) :
    let H (u : FiniteUnits F S) := L (sLocalBruhatFiniteSlice F S (fun v => (u v).val) f) *
      ∏ v : S, ((χ v (u v) : ℂ) * finiteZetaWeight F v.val z (u v))
    Integrable H (Measure.pi μ) ∧
      L (sLocalFiniteZetaSchwartzTest F S μ χ z f) = ∫ u, H u ∂Measure.pi μ := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  let H (g : sLocalBruhatImage F S) (u : FiniteUnits F S) :=
    L (sLocalBruhatFiniteSlice F S (fun v => (u v).val) g) *
      ∏ v : S, ((χ v (u v) : ℂ) * finiteZetaWeight F v.val z (u v))
  let T := L.comp (sLocalFiniteZetaSchwartzTest F S μ χ z)
  change Integrable (H f) (Measure.pi μ) ∧ T f = ∫ u, H f u ∂Measure.pi μ
  have hf : f ∈ Submodule.span ℂ {g : sLocalBruhatImage F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, ψ, rfl⟩ := hg
    have he : H (sLocalBruhatPure F S φ ψ) =
        fun u => L φ * sLocalFiniteZetaIntegrand F S χ ψ z u := by
      funext u
      dsimp [H, sLocalBruhatFiniteSlice]
      rw [sLocalBruhatContractFinite_pure, map_smul]
      change ψ.val (fun v => (u v).val) * L φ * _ = _
      let w := ∏ v : S, ((χ v (u v) : ℂ) * finiteZetaWeight F v.val z (u v))
      change (ψ.val (fun v => (u v).val) * L φ) * w =
        L φ * (ψ.val (fun v => (u v).val) * w)
      ac_rfl
    rw [he]
    obtain ⟨hI, hvalue⟩ := sLocalFiniteZetaContinued_eq_integral F S μ χ ψ z hz
    refine ⟨hI.const_mul _, ?_⟩
    change L (sLocalBruhatContractFinite F S
      (sLocalFiniteZetaContinued F S μ χ z).toLinearMap (sLocalBruhatPure F S φ ψ)) = _
    rw [sLocalBruhatContractFinite_pure, map_smul, integral_const_mul]
    change sLocalFiniteZetaContinued F S μ χ z ψ * L φ = _
    rw [hvalue, mul_comm]
  | zero =>
    have he : H 0 = 0 := by funext u; simp [H]
    simp [he]
  | add a b _ _ ha hb =>
    have he : H (a + b) = fun u => H a u + H b u := by
      funext u
      simp only [H, map_add, add_mul]
    rw [he]
    exact ⟨ha.1.add hb.1, by rw [map_add, integral_add ha.1 hb.1, ha.2, hb.2]⟩
  | smul c a _ ha =>
    have he : H (c • a) = fun u => c * H a u := by
      funext u
      simp only [H, map_smul, smul_eq_mul, mul_assoc]
    rw [he]
    exact ⟨ha.1.const_mul c, by rw [map_smul, smul_eq_mul, integral_const_mul, ha.2]⟩

local instance : MeasurableSpace (SIdeles F S) := borel _
local instance : BorelSpace (SIdeles F S) := ⟨rfl⟩

local instance (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ := by
  letI : SecondCountableTopology (v.val.adicCompletion F) := finitePlace_secondCountable F v.val
  letI : SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
variable (μarch : Measure (ArchUnits F))

local instance : MeasurableMul (ArchUnits F) :=
  ⟨fun a => ((continuous_const (y := a)).mul continuous_id).measurable,
    fun a => (continuous_id.mul (continuous_const (y := a))).measurable⟩

local instance (v : S) : MeasurableMul (v.val.adicCompletion F)ˣ :=
  ⟨fun a => ((continuous_const (y := a)).mul continuous_id).measurable,
    fun a => (continuous_id.mul (continuous_const (y := a))).measurable⟩

local instance : MeasurableMul (FiniteUnits F S) :=
  ⟨fun a => ((continuous_const (y := a)).mul continuous_id).measurable,
    fun a => (continuous_id.mul (continuous_const (y := a))).measurable⟩

/-- Transport the product of archimedean and selected finite Haar measures
to the actual S-idele group. -/
def sLocalZetaProductMeasure : Measure (SIdeles F S) :=
  (μarch.prod (Measure.pi μ)).map (sLocalZetaIdeleCoordinates F S).symm

theorem sLocalZetaProductMeasure_isHaar [μarch.IsHaarMeasure] [SigmaFinite μarch] :
    (sLocalZetaProductMeasure F S μ μarch).IsHaarMeasure := by
  unfold sLocalZetaProductMeasure
  exact ContinuousMulEquiv.isHaarMeasure_map (μ := μarch.prod (Measure.pi μ))
    (sLocalZetaIdeleCoordinates F S).symm

/-- The archimedean integral appearing after splitting the S-ideles. -/
def sLocalArchZetaIntegral (ω : PontryaginDual (NormOne F S)) (φ : ArchTests F) (z : ℂ) : ℂ :=
  ∫ a, sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) *
    φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val) ∂μarch

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)] in
private theorem sLocalArchZetaIntegrand_coordinates (ω : PontryaginDual (NormOne F S))
    (φ : ArchTests F) (z : ℂ)
    (p : (ZetaRealPlaces F → ℝˣ) × (ZetaComplexPlaces F → ℂˣ)) :
    let a := (infiniteAdeleUnitsCoordinates F).symm p
    sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) *
        φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val) =
      ((∏ v, sLocalRealArchWeight F S ω v z (p.1 v)) *
        ∏ v, sLocalComplexArchWeight F S ω v z (p.2 v)) *
        φ (fun v => (p.1 v : ℝ), fun v => (p.2 v : ℂ)) := by
  let e := infiniteAdeleUnitsCoordinates F
  let a := e.symm p
  have hp : e a = p := e.apply_symm_apply p
  change sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) * _ = _
  have hw := sLocalArchZetaWeight_eq_product F S ω z a
  dsimp only at hw
  change _ = (∏ v : ZetaRealPlaces F, sLocalRealArchWeight F S ω v z ((e a).1 v)) *
    ∏ v : ZetaComplexPlaces F, sLocalComplexArchWeight F S ω v z ((e a).2 v) at hw
  rw [hp] at hw
  rw [← hw]
  congr 1
  apply congrArg φ
  apply Prod.ext
  · funext v
    simpa only [(show infiniteAdeleUnitsCoordinates F a = p from hp)] using
      (infiniteAdeleUnitsCoordinates_real_val F a v).symm
  · funext v
    simpa only [(show infiniteAdeleUnitsCoordinates F a = p from hp)] using
      (infiniteAdeleUnitsCoordinates_complex_val F a v).symm

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ] in
/-- The actual archimedean Haar integral, in the product of normalized
real and complex unit coordinates. -/
theorem sLocalArchZetaIntegral_eq_productCoordinates (ω : PontryaginDual (NormOne F S))
    (φ : ArchTests F) (z : ℂ) :
    sLocalArchZetaIntegral F S (archimedeanMultiplicativeHaar F) ω φ z =
      ∫ p : (ZetaRealPlaces F → ℝˣ) × (ZetaComplexPlaces F → ℂˣ),
        ((∏ v : ZetaRealPlaces F, sLocalRealArchWeight F S ω v z (p.1 v)) *
          ∏ v : ZetaComplexPlaces F, sLocalComplexArchWeight F S ω v z (p.2 v)) *
        φ (fun v => ((p.1 v : ℝˣ) : ℝ), fun v => ((p.2 v : ℂˣ) : ℂ))
        ∂archimedeanCoordinateMeasure F := by
  rw [sLocalArchZetaIntegral, archimedeanMultiplicativeHaar_integral]
  exact integral_congr_ae (.of_forall (sLocalArchZetaIntegrand_coordinates F S ω φ z))

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ] in
/-- Absolute convergence of the archimedean S-idelic integral on the
positive half-plane for every joint Schwartz test. -/
theorem sLocalArchZeta_integrable (ω : PontryaginDual (NormOne F S))
    (φ : ArchTests F) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun a : ArchUnits F =>
      sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) *
        φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)) (archimedeanMultiplicativeHaar F) := by
  have hR (v : ZetaRealPlaces F) : 0 < (z + (sLocalRealArchParameters F S ω v).1).re := by
    simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  have hC (v : ZetaComplexPlaces F) : 0 < (z + (sLocalComplexArchParameters F S ω v).1).re := by
    simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz
  apply (archimedeanMultiplicativeHaar_integrable_iff F _).2
  refine (archimedeanNumberFieldZeta_integrable_product F
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z hR hC φ).congr ?_
  exact .of_forall fun p => by
    simpa only [sLocalRealArchWeight, sLocalComplexArchWeight,
      realArchUnitWeight, complexArchUnitWeight, Real.norm_eq_abs] using
        (sLocalArchZetaIntegrand_coordinates F S ω φ z p).symm

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)] in
private theorem sLocalIdelicZetaIntegrand_coordinates (ω : PontryaginDual (NormOne F S))
    (z : ℂ) (f : sLocalBruhatImage F S) (a : ArchUnits F) (u : FiniteUnits F S) :
    sLocalIdelicZetaIntegrand F S ω z f ((sLocalZetaIdeleCoordinates F S).symm (a, u)) =
      (sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) *
        sLocalBruhatFiniteSlice F S (fun v => (u v).val) f
          (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)) *
        ∏ v : S, ((sLocalFiniteZetaPhases F S ω v (u v) : ℂ) *
          finiteZetaWeight F v.val z (u v)) := by
  rw [sLocalIdelicZetaIntegrand, sLocalZetaWeight_product, sLocalZetaIdeleCoordinates_val,
    sLocalBruhatFiniteSlice_apply]
  ac_rfl

/-- Fubini on the actual S-idele group. The inner archimedean integral is
evaluated on the genuine finite slice of the given test. -/
theorem sLocalIdelicZetaIntegral_eq_finiteSlices [μarch.IsHaarMeasure] [SigmaFinite μarch]
    (ω : PontryaginDual (NormOne F S))
    (f : sLocalBruhatImage F S) (z : ℂ) (hz : 0 < z.re) :
    sLocalIdelicZetaIntegral F S (sLocalZetaProductMeasure F S μ μarch) ω f z =
      ∫ u : FiniteUnits F S,
        sLocalArchZetaIntegral F S μarch ω (sLocalBruhatFiniteSlice F S (fun v => (u v).val) f) z *
          ∏ v : S, ((sLocalFiniteZetaPhases F S ω v (u v) : ℂ) * finiteZetaWeight F v.val z (u v))
        ∂Measure.pi μ := by
  let ν := sLocalZetaProductMeasure F S μ μarch
  letI : ν.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ μarch
  obtain ⟨κ, hκ, hcompat⟩ := sLocalClassHaar_exists_weil F S ν
  letI := hκ
  have hI := (sLocalIdelicZeta_integrable_eq_theta F S ν κ hcompat ω f z hz).1
  let e := (sLocalZetaIdeleCoordinates F S).symm.toHomeomorph.toMeasurableEquiv
  let A := sLocalIdelicZetaIntegrand F S ω z f
  have hi : Integrable (fun p => A (e p)) (μarch.prod (Measure.pi μ)) :=
    (integrable_map_equiv e A).mp hI
  change (∫ g, A g ∂(μarch.prod (Measure.pi μ)).map e) = _
  rw [integral_map_equiv, integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    let W := ∏ v : S, ((sLocalFiniteZetaPhases F S ω v (u v) : ℂ) *
      finiteZetaWeight F v.val z (u v))
    let M (a : ArchUnits F) :=
      sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) *
        sLocalBruhatFiniteSlice F S (fun v => (u v).val) f
          (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)
    have heq : (∫ a, (A ∘ e) (a, u) ∂μarch) = ∫ a, M a * W ∂μarch :=
      integral_congr_ae (Eventually.of_forall fun a =>
        sLocalIdelicZetaIntegrand_coordinates F S ω z f a u)
    change (∫ a, (A ∘ e) (a, u) ∂μarch) = (∫ a, M a ∂μarch) * W
    rw [heq, integral_mul_const]

/-- Evaluation of the product measure on a pure Bruhat tensor, allowing
an arbitrary archimedean Schwartz factor. -/
theorem sLocalIdelicZetaIntegral_pure_product [μarch.IsHaarMeasure] [SigmaFinite μarch]
    (ω : PontryaginDual (NormOne F S)) (φ : ArchTests F)
    (h : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)) (z : ℂ) (hz : 0 < z.re) :
    sLocalIdelicZetaIntegral F S (sLocalZetaProductMeasure F S μ μarch) ω
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct h)) z =
      sLocalArchZetaIntegral F S μarch ω φ z *
        ∏ v : S, finiteZetaIntegral F v.val (μ v) (sLocalFiniteZetaPhases F S ω v) (h v) z := by
  let p := sLocalBruhatPure F S φ (locallyConstantTestPiProduct h)
  rw [sLocalIdelicZetaIntegral_eq_finiteSlices F S μ μarch ω p z hz]
  have hArch (u : FiniteUnits F S) :
      sLocalArchZetaIntegral F S μarch ω
        (sLocalBruhatFiniteSlice F S (fun v => (u v).val) p) z =
      (sLocalArchZetaIntegral F S μarch ω φ z) * ∏ v : S, (h v).val (u v).val := by
    unfold sLocalArchZetaIntegral
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun a => by
      dsimp only [p]
      rw [sLocalBruhatFiniteSlice_apply, sLocalBruhatPure_restrict,
        locallyConstantTestPiProduct_apply, mul_assoc]
  simp_rw [hArch, mul_assoc, ← Finset.prod_mul_distrib]
  rw [integral_const_mul]
  congr 1
  simp_rw [← mul_assoc]
  exact integral_fintype_prod_eq_prod (μ := μ) (fun (v : S) (u : (v.val.adicCompletion F)ˣ) =>
    (h v).val u.val * (sLocalFiniteZetaPhases F S ω v u : ℂ) * finiteZetaWeight F v.val z u)

/-- The meromorphic product of the normalized archimedean local factors
and the given finite factors, acting on the actual S-local test space. -/
def sLocalProductZetaContinued
    (ω : PontryaginDual (NormOne F S))
    (a : {w : InfinitePlace F // w.IsReal} → ℂ × ℕ)
    (j : {w : InfinitePlace F // w.IsComplex} → ℂ × ℤ)
    (f : sLocalBruhatImage F S) (z : ℂ) : ℂ :=
  archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z
    (sLocalFiniteZetaSchwartzTest F S μ (sLocalFiniteZetaPhases F S ω) z f)

omit [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)] in
theorem sLocalProductZetaContinued_meromorphic
    (ω : PontryaginDual (NormOne F S))
    (a : {w : InfinitePlace F // w.IsReal} → ℂ × ℕ)
    (j : {w : InfinitePlace F // w.IsComplex} → ℂ × ℤ)
    (f : sLocalBruhatImage F S) :
    Meromorphic (sLocalProductZetaContinued F S μ ω a j f) :=
  sLocalFiniteZetaSchwartzTest_meromorphic F S μ _
    (archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j)
    (archimedeanNumberFieldZeta_meromorphic F complexTamagawaAngularMeasure a j) f

omit [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)] in
/-- Clearing the finite Euler denominator gives a bounded S-local continuation
on a closed strip at sufficiently large heights in every archimedean coordinate. -/
theorem sLocalProductZeta_finiteCleared_norm_le_on_strip
    (ω : PontryaginDual (NormOne F S)) (f : sLocalBruhatImage F S) (l r : ℝ) :
    let a := sLocalRealArchParameters F S ω
    let j := sLocalComplexArchParameters F S ω
    let D := sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
      (∀ i, 1 ≤ |(z + (j i).1).im|) → (∀ i, 1 ≤ |(z + (a i).1).im|) →
      D z ≠ 0 → ‖D z * sLocalProductZetaContinued F S μ ω a j f z‖ ≤ C := by
  intro a j D
  let χ := sLocalFiniteZetaPhases F S ω
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  have hf : f ∈ Submodule.span ℂ {g : sLocalBruhatImage F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, ψ, rfl⟩ := hg
    obtain ⟨p, hp, hArch⟩ :=
      archimedeanNumberFieldZeta_uniform_seminorm F complexTamagawaAngularMeasure a j l r
    obtain ⟨C, hC, hFin⟩ := sLocalFiniteZetaCleared_norm_le_on_strip F S μ χ ψ l r
    refine ⟨C * p φ, mul_nonneg hC (apply_nonneg _ _), fun z hz hj ha hd ↦ ?_⟩
    let N := sLocalFiniteZetaCleared F S μ χ z ψ
    let A := archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ
    have hEq : D z * sLocalProductZetaContinued F S μ ω a j
        (sLocalBruhatPure F S φ ψ) z = N * A := by
      rw [sLocalProductZetaContinued, sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure, map_smul]
      change D z * ((D z)⁻¹ * N * A) = N * A
      calc
        _ = (D z * (D z)⁻¹) * (N * A) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hd, one_mul]
    rw [hEq, norm_mul]
    exact mul_le_mul (hFin z hz) (hArch z hz hj ha φ) (norm_nonneg _) hC
  | zero =>
    exact ⟨0, le_rfl, fun z _ _ _ _ ↦ by simp [sLocalProductZetaContinued]⟩
  | add f g _ _ hf hg =>
    obtain ⟨C, hC, hf⟩ := hf
    obtain ⟨B, hB, hg⟩ := hg
    refine ⟨C + B, add_nonneg hC hB, fun z hz hj ha hd ↦ ?_⟩
    have he : sLocalProductZetaContinued F S μ ω a j (f + g) z =
        sLocalProductZetaContinued F S μ ω a j f z + sLocalProductZetaContinued F S μ ω a j g z := by
      simp only [sLocalProductZetaContinued, map_add]
    rw [he, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hf z hz hj ha hd) (hg z hz hj ha hd))
  | smul c f _ hf =>
    obtain ⟨C, hC, hf⟩ := hf
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun z hz hj ha hd ↦ ?_⟩
    have hc : sLocalProductZetaContinued F S μ ω a j (c • f) z =
        c * sLocalProductZetaContinued F S μ ω a j f z := by
      rw [sLocalProductZetaContinued, map_smul, map_smul]
      rfl
    rw [hc, mul_left_comm, norm_mul]
    exact mul_le_mul_of_nonneg_left (hf z hz hj ha hd) (norm_nonneg _)

/-- A meromorphic joint archimedean family, once supplied, gives the
continuation of the actual S-local integral for every Schwartz–Bruhat test. -/
theorem sLocalIdelicZeta_continuation_of_archimedean [μarch.IsHaarMeasure] [SigmaFinite μarch]
    (ω : PontryaginDual (NormOne F S))
    (L : ℂ → ArchTests F →L[ℂ] ℂ)
    (hL : ∀ φ, Meromorphic (fun z => L z φ))
    (h0 : ∀ (z : ℂ), 0 < z.re → ∀ φ, L z φ = sLocalArchZetaIntegral F S μarch ω φ z)
    (f : sLocalBruhatImage F S) :
    let Z z := L z (sLocalFiniteZetaSchwartzTest F S μ (sLocalFiniteZetaPhases F S ω) z f)
    Meromorphic Z ∧ EqOn Z (sLocalIdelicZetaIntegral F S (sLocalZetaProductMeasure F S μ μarch) ω f)
      {z | 0 < z.re} := by
  refine ⟨sLocalFiniteZetaSchwartzTest_meromorphic F S μ _ L hL f, fun z hz => ?_⟩
  rw [sLocalIdelicZetaIntegral_eq_finiteSlices F S μ μarch ω f z hz]
  have he := (sLocalFiniteZetaSchwartzTest_eq_integral F S μ (sLocalFiniteZetaPhases F S ω) (L z) f z hz).2
  simp_rw [h0 z hz] at he
  exact (h0 z hz _).trans he

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ] in
/-- The composed meromorphic archimedean zeta family extends the original
S-local Haar integral. -/
theorem archimedeanNumberFieldZeta_eq_sLocalArchZetaIntegral
    (ω : PontryaginDual (NormOne F S)) (φ : ArchTests F) {z : ℂ} (hz : 0 < z.re) :
    archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
        (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z φ =
      sLocalArchZetaIntegral F S (archimedeanMultiplicativeHaar F) ω φ z := by
  have hR (v : ZetaRealPlaces F) : 0 < (z + (sLocalRealArchParameters F S ω v).1).re := by
    simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  have hC (v : ZetaComplexPlaces F) : 0 < (z + (sLocalComplexArchParameters F S ω v).1).re := by
    simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz
  rw [archimedeanNumberFieldZeta_eq_productIntegral _ _ _ _ hR hC,
    sLocalArchZetaIntegral_eq_productCoordinates]
  simp only [sLocalRealArchWeight, sLocalComplexArchWeight, realArchUnitWeight,
    complexArchUnitWeight, Real.norm_eq_abs]

/-- The actual S-local idelic zeta integral has a meromorphic continuation
on every fixed unitary component, with the transported product Haar measure. -/
theorem sLocalIdelicZeta_meromorphic_continuation
    (ω : PontryaginDual (NormOne F S)) (f : sLocalBruhatImage F S) :
    let Z := sLocalProductZetaContinued F S μ ω
      (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) f
    Meromorphic Z ∧ EqOn Z (sLocalIdelicZetaIntegral F S
      (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)) ω f)
      {z | 0 < z.re} :=
  sLocalIdelicZeta_continuation_of_archimedean F S μ (archimedeanMultiplicativeHaar F) ω
    (archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
      (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω))
    (archimedeanNumberFieldZeta_meromorphic F complexTamagawaAngularMeasure _ _)
    (fun _ hz φ => archimedeanNumberFieldZeta_eq_sLocalArchZetaIntegral F S ω φ hz) f

include μ in
/-- Changing multiplicative Haar normalization preserves meromorphic
continuation on every S-local unitary component. -/
theorem sLocalIdelicZeta_exists_meromorphic_continuation
    (η : Measure (SIdeles F S)) [η.IsHaarMeasure]
    (ω : PontryaginDual (NormOne F S)) (f : sLocalBruhatImage F S) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      EqOn Z (sLocalIdelicZetaIntegral F S η ω f) {z | 0 < z.re} := by
  letI : LocallyCompactSpace (SIdeles F S) := sLocalIdeles_locallyCompact F S
  letI : SecondCountableTopology (SIdeles F S) := sLocalIdeles_secondCountable F S
  let ν := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : ν.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  let c := Measure.haarScalarFactor η ν
  have he : η = c • ν := Measure.isMulLeftInvariant_eq_smul η ν
  let Z := sLocalProductZetaContinued F S μ ω
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) f
  have h := sLocalIdelicZeta_meromorphic_continuation F S μ ω f
  refine ⟨fun z => (c : ℝ) • Z z, ?_, fun z hz => ?_⟩
  · simp only [Complex.real_smul]
    change Meromorphic ((c : ℂ) • Z)
    exact h.1.const_smul _
  · change (c : ℝ) • Z z = _
    rw [sLocalIdelicZetaIntegral, he, integral_smul_nnreal_measure, ← sLocalIdelicZetaIntegral, ← h.2 hz,
      NNReal.smul_def]

attribute [local instance] sLocalZetaUnfolding_classMeasurable

include μ in
/-- The same meromorphic continuation extends the quotient theta Mellin
integral when the Haar measures are compatible under Weil unfolding. -/
theorem sLocalThetaZeta_exists_meromorphic_continuation
    (η : Measure (SIdeles F S)) [η.IsHaarMeasure]
    (ν : Measure (NormOne F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) η Measure.count (sLocalClassHaar F S ν))
    (ω : PontryaginDual (NormOne F S)) (f : sLocalBruhatImage F S) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      EqOn Z (sLocalThetaZetaIntegral F S ν ω f) {z | 0 < z.re} := by
  obtain ⟨Z, hZ, he⟩ := sLocalIdelicZeta_exists_meromorphic_continuation F S μ η ω f
  exact ⟨Z, hZ, fun z hz => (he hz).trans (sLocalIdelicZeta_integrable_eq_theta F S η ν hν ω f z hz).2⟩

include μ in
/-- The same continuation extends the homogeneous radial Mellin integral
for every homomorphic section of the S-idelic modulus. -/
theorem sLocalRadialZeta_exists_meromorphic_continuation
    (η : Measure (SIdeles F S)) [η.IsHaarMeasure]
    (ν : Measure (NormOne F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) η Measure.count (sLocalClassHaar F S ν))
    (τ : Multiplicative ℝ →* SIdeles F S)
    (hτ : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (ω : PontryaginDual (NormOne F S)) (f : sLocalBruhatImage F S) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧ EqOn Z (fun z =>
      ∫ t : ℝ, let q : SClasses F S := QuotientGroup.mk (τ (Multiplicative.ofAdd t))
        sLocalZetaWeight F S ω z q * sLocalHomogeneousTheta F S ν ω f.val q)
      {z | 0 < z.re} := by
  obtain ⟨Z, hZ, he⟩ := sLocalIdelicZeta_exists_meromorphic_continuation F S μ η ω f
  exact ⟨Z, hZ, fun z hz => (he hz).trans (sLocalIdelicZeta_eq_radial F S η ν hν τ hτ ω f z hz)⟩

end

end Masullo
