import AdelicOrbitBoundary
import IdelicArchimedeanCharacters

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField RestrictedProduct

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

omit [NumberField F] in
private theorem fixes_archimedeanCoordinatePoint_iff {B : Type*} [CommRing B]
    (v : InfinitePlace F) (a : InfiniteAdeleRing F × B) :
    a * (archimedeanCoordinateLine F v 0, 1) = (archimedeanCoordinateLine F v 0, 1) ↔
      (∀ w ≠ v, a.1 w = 1) ∧ a.2 = 1 := by
  constructor
  · intro h
    refine ⟨fun w hw ↦ ?_, ?_⟩
    · have he := congrArg (fun p : InfiniteAdeleRing F × B ↦ p.1 w) h
      change a.1 w * archimedeanCoordinateLine F v 0 w =
        archimedeanCoordinateLine F v 0 w at he
      simpa [archimedeanCoordinateLine, hw] using he
    · have he := congrArg Prod.snd h
      simpa using he
  · rintro ⟨h, ht⟩
    apply Prod.ext
    · funext w
      change a.1 w * archimedeanCoordinateLine F v 0 w =
        archimedeanCoordinateLine F v 0 w
      by_cases hw : w = v
      · subst w
        simp [archimedeanCoordinateLine]
      · simp [archimedeanCoordinateLine, hw, h w hw]
    · simpa using ht

private theorem unit_orbit_normOne {R : Type*} [CommMonoid R]
    (N : Rˣ →* ℝ) (hN : ∀ g, 0 < N g) (z : R)
    (s : Multiplicative ℝ →* Rˣ) (hs : ∀ t, N (s t) = Real.exp t.toAdd)
    (hfix : ∀ t, (s t).val * z = z) :
    Set.range (fun g : N.ker ↦ g.val.val * z) = Set.range (fun g : Rˣ ↦ g.val * z) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro _ ⟨g, rfl⟩
    let t := Multiplicative.ofAdd (Real.log (N g))
    have hh : g / s t ∈ N.ker := by
      change N (g / s t) = 1
      rw [map_div, hs]
      change N g / Real.exp (Real.log (N g)) = 1
      rw [Real.exp_log (hN g), div_self (hN g).ne']
    refine ⟨⟨g / s t, hh⟩, ?_⟩
    calc
      (g / s t).val * z = (g / s t).val * ((s t).val * z) := by rw [hfix]
      _ = ((g / s t) * s t).val * z := by simp only [Units.val_mul, mul_assoc]
      _ = g.val * z := by rw [div_mul_cancel]

private theorem onePlaceExpSection_fixes (v : InfinitePlace F) (t : Multiplicative ℝ) :
    (onePlaceExpSection F v t).val * adelicCoordinatePoint F (.inl v) =
      adelicCoordinatePoint F (.inl v) := by
  apply (fixes_archimedeanCoordinatePoint_iff F v _).mpr
  constructor
  · intro w h
    rw [onePlaceExpSection, (archimedeanExpSection_components F _ _).1]
    simp [h]
  · exact (archimedeanExpSection_components F _ t).2

/-- The global norm-one ideles act transitively on the orbit of an infinite coordinate point. -/
theorem adelic_archimedean_normOne_orbit (v : InfinitePlace F) :
    Set.range (fun g : (ideleNorm F).ker ↦ g.val.val * adelicCoordinatePoint F (.inl v)) =
      Set.range (fun g : Idele F ↦ g.val * adelicCoordinatePoint F (.inl v)) :=
  unit_orbit_normOne (ideleNorm F) (ideleNorm_pos F) _ (onePlaceExpSection F v)
    (ideleNorm_onePlaceExpSection F v) (onePlaceExpSection_fixes F v)

private theorem project_archimedeanCoordinatePoint (S : Finset (Place F)) (v : InfinitePlace F) :
    sAdelesProjection F S (adelicCoordinatePoint F (.inl v)) = sAdelicCoordinatePoint F S (.inl v) := by
  apply Prod.ext rfl
  funext w
  change ((1 : FiniteAdeleRing (𝓞 F) F) w.val) = 1
  rfl

/-- The local norm-one ideles act transitively on the corresponding S-local orbit. -/
theorem sAdelic_archimedean_normOne_orbit (S : Finset (Place F)) (v : InfinitePlace F) :
    Set.range (fun g : (sLocalIdeleNorm F S).ker ↦
      g.val.val * sAdelicCoordinatePoint F S (.inl v)) =
      Set.range (fun g : (SAdeles F S)ˣ ↦ g.val * sAdelicCoordinatePoint F S (.inl v)) := by
  apply unit_orbit_normOne (sLocalIdeleNorm F S)
    (fun g ↦ ideleNorm_pos F (sLocalEmbed F S g).val) _ (sOnePlaceExpSection F S v)
    (sLocalIdeleNorm_sOnePlaceExpSection F S v)
  intro t
  have h := congrArg (sAdelesProjection F S) (onePlaceExpSection_fixes F v t)
  rw [map_mul, project_archimedeanCoordinatePoint] at h
  exact h

private theorem fixes_unit_multiple_iff {R : Type*} [CommMonoid R]
    (g a : Rˣ) (z : R) : a.val * (g.val * z) = g.val * z ↔ a.val * z = z := by
  rw [mul_left_comm]
  exact g.isUnit.mul_right_inj

private theorem ideleNorm_of_archimedean_coordinates (v : InfinitePlace F) (a : Idele F)
    (h : (∀ w ≠ v, a.val.1 w = 1) ∧ a.val.2 = 1) :
    ideleNorm F a = ‖a.val.1 v‖ ^ v.mult := by
  change (∏ w : InfinitePlace F, ‖a.val.1 w‖ ^ w.mult) *
    (∏ᶠ w : Place F, ‖a.val.2 w‖) = _
  have hf : (∏ᶠ w : Place F, ‖a.val.2 w‖) = 1 := by
    rw [h.2]
    change (∏ᶠ _w : Place F, ‖(1 : _w.adicCompletion F)‖) = 1
    simp
  rw [hf, mul_one]
  exact Finset.prod_eq_single v (fun w _ hw ↦ by simp [h.1 w hw]) (by simp)

private theorem ideleNorm_finiteOne_projection (S : Finset (Place F)) (a : Idele F)
    (ha : a.val.2 = 1) :
    sLocalIdeleNorm F S (Units.map (sAdelesProjection F S) a) = ideleNorm F a := by
  have hb : a ∈ sIdeleBlock F S := by
    apply (sIdeleBlock_mem_iff F S a).mpr
    intro w _
    apply (ideleOrder_eq_zero_iff F a w).mpr
    rw [ha]
    exact map_one _
  exact sBlock_norm_eq F S ⟨a, hb⟩

private theorem singleInfiniteIdele_finiteOne (v : InfinitePlace F) (u : v.Completionˣ) :
    (singleInfiniteIdele F v u).val.2 = 1 := rfl

private theorem singleInfiniteIdele_arch (v w : InfinitePlace F) (u : v.Completionˣ) :
    (singleInfiniteIdele F v u).val.1 w =
      Function.update (fun j : InfinitePlace F ↦ (1 : j.Completion)) v u.val w := rfl

private theorem singleInfiniteIdele_norm (v : InfinitePlace F) (u : v.Completionˣ) :
    ideleNorm F (singleInfiniteIdele F v u) = ‖u.val‖ ^ v.mult := by
  have hn (w : InfinitePlace F) (hw : w ≠ v) :
      (singleInfiniteIdele F v u).val.1 w = 1 := by
    rw [singleInfiniteIdele_arch, Function.update_of_ne hw]
  rw [ideleNorm_of_archimedean_coordinates F v _ ⟨hn, singleInfiniteIdele_finiteOne F v u⟩,
    singleInfiniteIdele_arch, Function.update_self]

private def archUnitCoord (v : InfinitePlace F) (a : Idele F) : v.Completionˣ :=
  let e : Adeles F →* v.Completion :=
    { toFun := fun p ↦ p.1 v
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  Units.map e a

private def sArchUnitCoord (S : Finset (Place F)) (v : InfinitePlace F)
    (a : (SAdeles F S)ˣ) : v.Completionˣ :=
  Units.map (((Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v)).comp
    (RingHom.fst (InfiniteAdeleRing F) ((w : S) → w.val.adicCompletion F))) a

private theorem global_eq_single_of_fixes (v : InfinitePlace F) (a : Idele F)
    (h : a.val * adelicCoordinatePoint F (.inl v) = adelicCoordinatePoint F (.inl v)) :
    singleInfiniteIdele F v (archUnitCoord F v a) = a := by
  obtain ⟨hw, ht⟩ := (fixes_archimedeanCoordinatePoint_iff F v a.val).mp h
  apply Units.ext
  apply Prod.ext
  · funext w
    rw [singleInfiniteIdele_arch]
    by_cases he : w = v
    · subst w
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne he, hw _ he]
  · exact ht.symm

private theorem local_eq_single_of_fixes (S : Finset (Place F)) (v : InfinitePlace F)
    (a : (SAdeles F S)ˣ)
    (h : a.val * sAdelicCoordinatePoint F S (.inl v) = sAdelicCoordinatePoint F S (.inl v)) :
    Units.map (sAdelesProjection F S) (singleInfiniteIdele F v (sArchUnitCoord F S v a)) = a := by
  obtain ⟨hw, ht⟩ := (fixes_archimedeanCoordinatePoint_iff F v a.val).mp h
  apply Units.ext
  apply Prod.ext
  · funext w
    change (singleInfiniteIdele F v (sArchUnitCoord F S v a)).val.1 w = _
    rw [singleInfiniteIdele_arch]
    by_cases he : w = v
    · subst w
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne he, hw _ he]
  · exact ht.symm

/-- The stabilizer of any point of the global orbit is the inserted group of local units
of norm one. This is the stabilizer in Proposition 8.2.0.5. -/
theorem adelic_archimedean_stabilizer (v : InfinitePlace F) (g : Idele F) (a : Idele F) :
    (ideleNorm F a = 1 ∧ a.val * (g.val * adelicCoordinatePoint F (.inl v)) =
        g.val * adelicCoordinatePoint F (.inl v)) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧ singleInfiniteIdele F v u = a := by
  rw [fixes_unit_multiple_iff]
  constructor
  · rintro ⟨hN, hfix⟩
    let u := archUnitCoord F v a
    have he : singleInfiniteIdele F v u = a := global_eq_single_of_fixes F v a hfix
    rw [← he, singleInfiniteIdele_norm] at hN
    exact ⟨u, (pow_eq_one_iff_of_nonneg (norm_nonneg _) InfinitePlace.mult_ne_zero).mp hN, he⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨by rw [singleInfiniteIdele_norm, hu, one_pow], ?_⟩
    apply (fixes_archimedeanCoordinatePoint_iff F v _).mpr
    exact ⟨fun w hw ↦ by rw [singleInfiniteIdele_arch, Function.update_of_ne hw], rfl⟩

/-- The same embedded norm-one stabilizer on the S-local orbit. -/
theorem sAdelic_archimedean_stabilizer (S : Finset (Place F)) (v : InfinitePlace F)
    (g a : (SAdeles F S)ˣ) :
    (sLocalIdeleNorm F S a = 1 ∧ a.val * (g.val * sAdelicCoordinatePoint F S (.inl v)) =
        g.val * sAdelicCoordinatePoint F S (.inl v)) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        Units.map (sAdelesProjection F S) (singleInfiniteIdele F v u) = a := by
  rw [fixes_unit_multiple_iff]
  constructor
  · rintro ⟨hN, hfix⟩
    let u := sArchUnitCoord F S v a
    have he : Units.map (sAdelesProjection F S) (singleInfiniteIdele F v u) = a :=
      local_eq_single_of_fixes F S v a hfix
    rw [← he, ideleNorm_finiteOne_projection F S _ (singleInfiniteIdele_finiteOne F v u),
      singleInfiniteIdele_norm] at hN
    exact ⟨u, (pow_eq_one_iff_of_nonneg (norm_nonneg _) InfinitePlace.mult_ne_zero).mp hN, he⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [ideleNorm_finiteOne_projection F S _ (singleInfiniteIdele_finiteOne F v u),
        singleInfiniteIdele_norm, hu, one_pow]
    · have h := (adelic_archimedean_stabilizer F v 1 (singleInfiniteIdele F v u)).mpr
        ⟨u, hu, rfl⟩
      have he := congrArg (sAdelesProjection F S) h.2
      rw [Units.val_one, one_mul, map_mul, project_archimedeanCoordinatePoint] at he
      exact he

omit [NumberField F] in
/-- At a real place the stabilizer condition is exactly the two signs. -/
theorem real_archimedean_stabilizer_coordinate (v : InfinitePlace F) (hv : v.IsReal)
    (u : v.Completionˣ) :
    ‖u.val‖ = 1 ↔ InfinitePlace.Completion.ringEquivRealOfIsReal hv u.val = 1 ∨
      InfinitePlace.Completion.ringEquivRealOfIsReal hv u.val = -1 := by
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hv
  have he : ‖e u.val‖ = ‖u.val‖ := e.isometry.norm_map_of_map_zero (map_zero
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv)) u.val
  rw [← he]
  change |e u.val| = 1 ↔ e u.val = 1 ∨ e u.val = -1
  exact abs_eq (by norm_num)

omit [NumberField F] in
/-- At a complex place the stabilizer condition is exactly the unit circle. -/
theorem complex_archimedean_stabilizer_coordinate (v : InfinitePlace F) (hv : v.IsComplex)
    (u : v.Completionˣ) :
    ‖u.val‖ = 1 ↔ ∃ z : Circle,
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hv u.val = (z : ℂ) := by
  let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
  have he : ‖e u.val‖ = ‖u.val‖ := e.isometry.norm_map_of_map_zero (map_zero
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)) u.val
  rw [← he]
  constructor
  · intro h
    exact ⟨⟨e u.val, mem_sphere_zero_iff_norm.mpr h⟩, rfl⟩
  · rintro ⟨z, hz⟩
    change e u.val = (z : ℂ) at hz
    rw [hz, Circle.norm_coe]

end Masullo
