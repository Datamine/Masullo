import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Compactness.LocallyCompact

open Filter Function Set Topology
open scoped Classical BigOperators

noncomputable section

namespace Masullo

variable {I : Type*} [Fintype I] (K : I → Type*)
  [∀ i, NormedField (K i)]

/-- A label specifies the omitted coordinate. The unmarked label has no zero coordinate. -/
def finiteCoordinateLabel (o : Option I) : ∀ i, K i :=
  fun i ↦ if o = some i then 0 else 1

def finiteCoordinateNorm (d : I → ℕ) (x : ∀ i, K i) : ℝ :=
  ∏ i, ‖x i‖ ^ d i

theorem finiteCoordinateNorm_continuous (d : I → ℕ) : Continuous (finiteCoordinateNorm K d) :=
  continuous_finsetProd _ fun i _ ↦ ((continuous_apply i).norm.pow _)

def finiteCoordinateUnitNorm (d : I → ℕ) : (∀ i, (K i)ˣ) →* ℝ where
  toFun u := finiteCoordinateNorm K d (fun i ↦ (u i).val)
  map_one' := by simp [finiteCoordinateNorm]
  map_mul' u v := by
    simp only [finiteCoordinateNorm, Pi.mul_apply, Units.val_mul, norm_mul, mul_pow,
      Finset.prod_mul_distrib]

section Orbits

variable (d : I → ℕ)

local notation "G" => MonoidHom.ker (finiteCoordinateUnitNorm K d)

def finiteCoordinateOrbitValue (g : G) (o : Option I) : ∀ i, K i :=
  fun i ↦ (g.val i).val * finiteCoordinateLabel K o i

def finiteCoordinateOrbitSpace : Set (∀ i, K i) :=
  range (fun p : G × Option I ↦ finiteCoordinateOrbitValue K d p.1 p.2)

def finiteCoordinateOrbitMap (p : G × Option I) : finiteCoordinateOrbitSpace K d :=
  ⟨_, mem_range_self p⟩

private theorem finiteCoordinateOrbitMap_surjective :
    Surjective (finiteCoordinateOrbitMap K d) := fun x ↦
  let ⟨p, hp⟩ := x.property
  ⟨p, Subtype.ext hp⟩

private theorem coordinateOrbit_eq_zero_iff (g : G) (o : Option I) (i : I) :
    finiteCoordinateOrbitValue K d g o i = 0 ↔ o = some i := by
  by_cases h : o = some i
  · simp [finiteCoordinateOrbitValue, finiteCoordinateLabel, h]
  · simp [finiteCoordinateOrbitValue, finiteCoordinateLabel, h, (g.val i).ne_zero]

private theorem coordinateOrbit_preserves_nonzero {i : I} (g : G) (o : Option I)
    (h : o ≠ some i) : finiteCoordinateOrbitValue K d g o i = (g.val i).val := by
  simp [finiteCoordinateOrbitValue, finiteCoordinateLabel, h]

private theorem coordinateLabel_unique {g g' : G} {o o' : Option I}
    (h : finiteCoordinateOrbitValue K d g o = finiteCoordinateOrbitValue K d g' o') :
    o = o' := by
  have hh (i : I) : o = some i ↔ o' = some i :=
    (coordinateOrbit_eq_zero_iff K d g o i).symm.trans
      (congrArg (fun x ↦ x i) h ▸ coordinateOrbit_eq_zero_iff K d g' o' i)
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some j => exact (hh j).mpr rfl
  | some i => exact ((hh i).mp rfl).symm

private def coordinateLabelOf (x : finiteCoordinateOrbitSpace K d) : Option I :=
  x.property.choose.2

private theorem coordinateLabelOf_orbit (g : G) (o : Option I) :
    coordinateLabelOf K d (finiteCoordinateOrbitMap K d (g, o)) = o :=
  coordinateLabel_unique K d (mem_range.mp (finiteCoordinateOrbitMap K d (g,o)).property).choose_spec

private theorem coordinateLabelOf_zero_iff (x : finiteCoordinateOrbitSpace K d) (i : I) :
    x.val i = 0 ↔ coordinateLabelOf K d x = some i := by
  have h := x.property.choose_spec
  change _ ↔ x.property.choose.2 = some i
  exact (Iff.of_eq (congrArg (fun y : ∀ j, K j ↦ y i = 0) h.symm)).trans
    (coordinateOrbit_eq_zero_iff K d _ _ _)

private theorem coordinateLabel_slice_open (hd : ∀ i, 0 < d i) (o : Option I) :
    IsOpen {x : finiteCoordinateOrbitSpace K d | coordinateLabelOf K d x = o} := by
  let X := finiteCoordinateOrbitSpace K d
  let V (i : I) := {x : X | x.val i ≠ 0}
  have hV (i : I) : IsOpen (V i) :=
    isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const
  have hunit (x : X) (hx : coordinateLabelOf K d x = none) :
      finiteCoordinateNorm K d x.val = 1 := by
    have he : x.val = fun i ↦ (x.property.choose.1.val i).val := by
      funext i
      refine (congrArg (fun y ↦ y i) x.property.choose_spec).symm.trans ?_
      apply coordinateOrbit_preserves_nonzero K d
      change coordinateLabelOf K d x ≠ some i
      rw [hx]
      simp
    rw [he]
    exact x.property.choose.1.property
  cases o with
  | none =>
    have he : {x : X | coordinateLabelOf K d x = none} = ⋂ i, V i := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, V]
      constructor
      · intro h i
        exact fun hz ↦ by simpa [h] using (coordinateLabelOf_zero_iff K d x i).mp hz
      · intro h
        cases eq : coordinateLabelOf K d x with
        | none => rfl
        | some i => exact (h i ((coordinateLabelOf_zero_iff K d x i).mpr eq)).elim
    rw [he]
    exact isOpen_iInter_of_finite hV
  | some j =>
    let W := {x : X | finiteCoordinateNorm K d x.val ≠ 1}
    have hW : IsOpen W :=
      isOpen_ne_fun ((finiteCoordinateNorm_continuous K d).comp continuous_subtype_val)
        continuous_const
    have he : {x : X | coordinateLabelOf K d x = some j} =
        W ∩ ⋂ i : {i // i ≠ j}, V i.val := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, V, W]
      constructor
      · intro h
        have hz := (coordinateLabelOf_zero_iff K d x j).mpr h
        have hb : finiteCoordinateNorm K d x.val = 0 := by
          unfold finiteCoordinateNorm
          apply Finset.prod_eq_zero (Finset.mem_univ j)
          rw [hz, norm_zero, zero_pow (hd j).ne']
        exact ⟨by rw [hb]; exact zero_ne_one, fun i hn ↦
          i.property (Option.some.inj (((coordinateLabelOf_zero_iff K d x i.val).mp hn).symm.trans h))⟩
      · rintro ⟨hN, hz⟩
        cases hh : coordinateLabelOf K d x with
        | none => exact (hN (hunit x hh)).elim
        | some i =>
          by_cases he : i = j
          · subst i; rfl
          · exact (hz ⟨i, he⟩ ((coordinateLabelOf_zero_iff K d x i).mpr hh)).elim
    rw [he]
    exact hW.inter (isOpen_iInter_of_finite fun i ↦ hV i.val)

private def asUnitOrOne {L : Type*} [NormedField L] (x : L) : Lˣ :=
  if h : x = 0 then 1 else Units.mk0 x h

private theorem asUnitOrOne_coe {L : Type*} [NormedField L] {x : L} (hx : x ≠ 0) :
    (asUnitOrOne x).val = x := by simp [asUnitOrOne, hx]

private theorem asUnitOrOne_continuousAt {L : Type*} [NormedField L] {x : L} (hx : x ≠ 0) :
    ContinuousAt (asUnitOrOne (L := L)) x := by
  apply Units.isEmbedding_val₀.isInducing.continuousAt_iff.mpr
  change Tendsto (fun t ↦ (asUnitOrOne t).val) (𝓝 x) (𝓝 (asUnitOrOne x).val)
  rw [asUnitOrOne_coe hx]
  apply tendsto_id.congr'
  filter_upwards [isOpen_ne_fun continuous_id (continuous_const (y := (0 : L))) |>.mem_nhds hx]
    with y hy
  exact (asUnitOrOne_coe hy).symm

private def missingNorm (i : I) (x : ∀ j, K j) : ℝ :=
  (∏ j ∈ Finset.univ.erase i, ‖x j‖ ^ d j)⁻¹

private theorem missingNorm_continuousAt (i : I) (x : ∀ j, K j) (hx : ∀ j ≠ i, x j ≠ 0) :
    ContinuousAt (missingNorm K d i) x := by
  unfold missingNorm
  apply ContinuousAt.inv₀
  · exact (continuous_finsetProd _ fun j _ ↦ (continuous_apply j).norm.pow _).continuousAt
  · exact Finset.prod_ne_zero_iff.mpr fun j hj ↦
      pow_ne_zero _ (norm_ne_zero_iff.mpr (hx j (Finset.ne_of_mem_erase hj)))

private theorem norm_split (i : I) (x : ∀ j, K j) :
    finiteCoordinateNorm K d x =
      ‖x i‖ ^ d i * ∏ j ∈ Finset.univ.erase i, ‖x j‖ ^ d j :=
  (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

private theorem missingNorm_on_orbit (i : I) (g : G) :
    missingNorm K d i (finiteCoordinateOrbitValue K d g (some i)) = ‖(g.val i).val‖ ^ d i := by
  have hprod : (∏ j ∈ Finset.univ.erase i, ‖finiteCoordinateOrbitValue K d g (some i) j‖ ^ d j) =
      ∏ j ∈ Finset.univ.erase i, ‖(g.val j).val‖ ^ d j := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [coordinateOrbit_preserves_nonzero K d g (some i)]
    exact fun h ↦ (Finset.ne_of_mem_erase hj) (Option.some.inj h).symm
  have he := g.property
  change finiteCoordinateNorm K d (fun j ↦ (g.val j).val) = 1 at he
  rw [norm_split K d i] at he
  unfold missingNorm
  rw [hprod]
  exact (eq_inv_of_mul_eq_one_left he).symm

private theorem liftOrbitValue_on_label (hd : ∀ i, 0 < d i)
    (hsection : ∀ (i : I) (u : (K i)ˣ), ∃ s : ℝ → (K i)ˣ,
      s (‖u.val‖ ^ d i) = u ∧ ContinuousAt s (‖u.val‖ ^ d i) ∧
        ∀ᶠ r in 𝓝 (‖u.val‖ ^ d i), (∃ v : (K i)ˣ, ‖v.val‖ ^ d i = r) →
          ‖(s r).val‖ ^ d i = r)
    (p : G × Option I) :
    ∃ L : finiteCoordinateOrbitSpace K d → G,
      Tendsto L (𝓝 (finiteCoordinateOrbitMap K d p)) (𝓝 p.1) ∧
        ∀ᶠ x in 𝓝 (finiteCoordinateOrbitMap K d p),
          finiteCoordinateOrbitMap K d (L x, p.2) = x := by
  let X := finiteCoordinateOrbitSpace K d
  let x₀ : X := finiteCoordinateOrbitMap K d p
  have hlabel : ∀ᶠ x in 𝓝 x₀, coordinateLabelOf K d x = p.2 :=
    (coordinateLabel_slice_open K d hd p.2).mem_nhds (coordinateLabelOf_orbit K d p.1 p.2)
  suffices h : ∃ L₀ : X → ∀ j, (K j)ˣ, Tendsto L₀ (𝓝 x₀) (𝓝 p.1.val) ∧
      ∀ᶠ x in 𝓝 x₀, ∃ g : G, g.val = L₀ x ∧ finiteCoordinateOrbitMap K d (g, p.2) = x by
    obtain ⟨L₀, h₀, h₁⟩ := h
    let L (x : X) : G := if hx : ∃ g : G, g.val = L₀ x ∧
        finiteCoordinateOrbitMap K d (g, p.2) = x then hx.choose else p.1
    have he : ∀ᶠ x in 𝓝 x₀, (L x).val = L₀ x ∧ finiteCoordinateOrbitMap K d (L x, p.2) = x := by
      filter_upwards [h₁] with x hx
      rw [show L x = hx.choose from dite_eq_left hx]
      exact hx.choose_spec
    exact ⟨L, tendsto_subtype_rng.mpr (h₀.congr' (he.mono fun _ hx ↦ hx.1.symm)),
      he.mono fun _ hx ↦ hx.2⟩
  have hcoord {j : I} (hj : p.2 ≠ some j) :
      Tendsto (fun x : X ↦ asUnitOrOne (x.val j)) (𝓝 x₀) (𝓝 (p.1.val j)) := by
    have he : x₀.val j = (p.1.val j).val := coordinateOrbit_preserves_nonzero K d _ _ hj
    have hn : x₀.val j ≠ 0 := he ▸ (p.1.val j).ne_zero
    have h := (asUnitOrOne_continuousAt hn).tendsto.comp
      (((continuous_apply j).comp continuous_subtype_val).tendsto x₀)
    rwa [show asUnitOrOne (x₀.val j) = p.1.val j from Units.ext ((asUnitOrOne_coe hn).trans he)] at h
  cases hp : p.2 with
  | none =>
    let L₀ (x : X) := fun j ↦ asUnitOrOne (x.val j)
    refine ⟨L₀, tendsto_pi_nhds.mpr (fun j ↦ hcoord (by simp [hp])), ?_⟩
    filter_upwards [hlabel] with x hx
    obtain ⟨⟨g, o⟩, hg⟩ := x.property
    have ho : o = p.2 := (coordinateLabelOf_orbit K d g o).symm.trans
      ((congrArg (coordinateLabelOf K d) (Subtype.ext hg)).trans hx)
    refine ⟨g, funext fun j ↦ Units.ext ?_, Subtype.ext ?_⟩
    · have he := (coordinateOrbit_preserves_nonzero K d g o (by simp [ho, hp])).symm.trans
        (congrArg (fun y ↦ y j) hg)
      exact he.trans (asUnitOrOne_coe (he ▸ (g.val j).ne_zero)).symm
    · change finiteCoordinateOrbitValue K d g none = x.val
      rw [← hp, ← ho]
      exact hg
  | some i =>
    obtain ⟨s, hs₀, hs, hs'⟩ := hsection i (p.1.val i)
    let L₀ (x : X) := Function.update (fun j ↦ asUnitOrOne (x.val j)) i (s (missingNorm K d i x.val))
    have hr : missingNorm K d i x₀.val = ‖(p.1.val i).val‖ ^ d i := by
      change missingNorm K d i (finiteCoordinateOrbitValue K d p.1 p.2) = _
      rw [hp]
      exact missingNorm_on_orbit K d i p.1
    have ht : Tendsto (fun x : X ↦ missingNorm K d i x.val) (𝓝 x₀)
        (𝓝 (‖(p.1.val i).val‖ ^ d i)) := by
      rw [← hr]
      apply (missingNorm_continuousAt K d i x₀.val ?_).tendsto.comp continuous_subtype_val.continuousAt
      intro j hj
      have he : x₀.val j = (p.1.val j).val :=
        coordinateOrbit_preserves_nonzero K d (i := j) p.1 p.2 (by simp [hp, Ne.symm hj])
      rw [he]
      exact (p.1.val j).ne_zero
    refine ⟨L₀, tendsto_pi_nhds.mpr ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        simpa [L₀, hs₀, Function.comp_def] using hs.tendsto.comp ht
      · simpa [L₀, Function.update_of_ne hj] using hcoord (by simp [hp, Ne.symm hj])
    · filter_upwards [hlabel, ht.eventually hs'] with x hx hrange
      obtain ⟨⟨g, o⟩, hg⟩ := x.property
      have ho : o = some i := (coordinateLabelOf_orbit K d g o).symm.trans
        ((congrArg (coordinateLabelOf K d) (Subtype.ext hg)).trans (hx.trans hp))
      have hri : missingNorm K d i x.val = ‖(g.val i).val‖ ^ d i := by
        rw [← hg]
        change missingNorm K d i (finiteCoordinateOrbitValue K d g o) = _
        rw [ho]
        exact missingNorm_on_orbit K d i g
      have hf : ‖(s (missingNorm K d i x.val)).val‖ ^ d i = ‖(g.val i).val‖ ^ d i :=
        (hrange ⟨g.val i, hri.symm⟩).trans hri
      have hout (j : I) (hj : j ≠ i) : (L₀ x j).val = (g.val j).val := by
        have he : x.val j = (g.val j).val :=
          (congrArg (fun y ↦ y j) hg).symm.trans
            (coordinateOrbit_preserves_nonzero K d g o (by simp [ho, Ne.symm hj]))
        change (Function.update (fun k ↦ asUnitOrOne (x.val k)) i
          (s (missingNorm K d i x.val)) j).val = _
        rw [Function.update_of_ne hj, he]
        exact asUnitOrOne_coe (g.val j).ne_zero
      have hn : finiteCoordinateUnitNorm K d (L₀ x) = 1 := by
        change (∏ j, ‖(L₀ x j).val‖ ^ d j) = 1
        calc
          _ = ∏ j, ‖(g.val j).val‖ ^ d j := by
            apply Finset.prod_congr rfl
            intro j _
            by_cases hj : j = i
            · subst j
              simpa [L₀] using hf
            · rw [hout j hj]
          _ = 1 := g.property
      refine ⟨⟨L₀ x, hn⟩, rfl, Subtype.ext (funext fun j ↦ ?_)⟩
      by_cases hj : j = i
      · subst j
        have hq : x.val i = 0 := (coordinateLabelOf_zero_iff K d x i).mpr (hx.trans hp)
        simp [finiteCoordinateOrbitMap, finiteCoordinateOrbitValue, finiteCoordinateLabel, hq]
      · have hq := (congrArg (fun y ↦ y j) hg).symm.trans
          (coordinateOrbit_preserves_nonzero K d g o (by simp [ho, Ne.symm hj]))
        exact (coordinateOrbit_preserves_nonzero K d (i := j) ⟨L₀ x, hn⟩ (some i) (by simp [Ne.symm hj])).trans
          ((hout j hj).trans hq.symm)


/-- Local continuous modulus choices in each factor make the finite-coordinate orbit map open. -/
theorem finiteCoordinateOrbitMap_openQuotient [TopologicalSpace (Option I)]
    [DiscreteTopology (Option I)] (hd : ∀ i, 0 < d i)
    (hsection : ∀ (i : I) (u : (K i)ˣ), ∃ s : ℝ → (K i)ˣ,
      s (‖u.val‖ ^ d i) = u ∧ ContinuousAt s (‖u.val‖ ^ d i) ∧
      ∀ᶠ r in 𝓝 (‖u.val‖ ^ d i), (∃ v : (K i)ˣ, ‖v.val‖ ^ d i = r) →
        ‖(s r).val‖ ^ d i = r) :
    IsOpenQuotientMap (finiteCoordinateOrbitMap K d) := by
  refine ⟨finiteCoordinateOrbitMap_surjective K d, ?_, ?_⟩
  · apply Continuous.subtype_mk
    exact continuous_pi fun i ↦
      (Units.continuous_val.comp ((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_fst))).mul
      ((continuous_of_discreteTopology (f := fun o : Option I ↦ finiteCoordinateLabel K o i)).comp
        continuous_snd)
  · intro U hU
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨L, hL, hh⟩ := liftOrbitValue_on_label K d hd hsection p
    have ht := hL.prodMk_nhds (tendsto_const_nhds (x := p.2))
    filter_upwards [ht.eventually (hU.mem_nhds hp), hh] with y hy he
    exact ⟨(L y, p.2), hy, he⟩

end Orbits

end Masullo
