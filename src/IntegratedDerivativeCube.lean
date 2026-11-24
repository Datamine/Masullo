import DerivativeUnitCube
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Count

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

private abbrev unitIntervalMeasure : Measure ℝ := volume.restrict (Icc 0 1)

local instance : IsProbabilityMeasure unitIntervalMeasure := ⟨by simp [unitIntervalMeasure]⟩

/-- The mixed derivative words indexed by subsets of the coordinates. -/
def cubeMixedPartials : (n : ℕ) → List (List (Fin n))
  | 0 => [[]]
  | n + 1 =>
    let tail := (cubeMixedPartials n).map (List.map Fin.succ)
    tail ++ tail.map (0 :: ·)

/-- Lebesgue measure restricted to the unit cube, of mass one. -/
abbrev unitDerivativeCube (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => unitIntervalMeasure

private theorem continuous_integrable_cube {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {f : (Fin n → ℝ) → V} (hf : Continuous f) :
    Integrable f (unitDerivativeCube n) := by
  rw [unitDerivativeCube, ← Measure.restrict_pi_pi]
  exact hf.continuousOn.integrableOn_compact
    (μ := Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (isCompact_univ_pi fun _ => isCompact_Icc)

private theorem norm_at_zero_le_integrals {f d : ℝ → ℂ} (hf : Continuous f) (hd : Continuous d)
    (h : ∀ t, HasDerivAt f (d t) t) :
    ‖f 0‖ ≤ (∫ t, ‖f t‖ ∂unitIntervalMeasure) + ∫ t, ‖d t‖ ∂unitIntervalMeasure := by
  have hi : Integrable (fun t => ‖d t‖) unitIntervalMeasure := hd.norm.integrableOn_Icc
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖f 0‖ ≤ ‖f t‖ + ∫ u, ‖d u‖ ∂unitIntervalMeasure := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun u _ => h u) (hd.intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le ht.1] at he
    calc
      ‖f 0‖ ≤ ‖f t‖ + ‖f t - f 0‖ := by
        simpa only [norm_sub_rev, add_sub_cancel] using norm_add_le (f t) (f 0 - f t)
      _ ≤ _ := add_le_add le_rfl (by
        rw [← he]
        exact (norm_integral_le_integral_norm _).trans
          (integral_mono_measure (Measure.restrict_mono
            (show Ioc (0 : ℝ) t ⊆ Icc 0 1 from fun _ hx => ⟨hx.1.le, hx.2.trans ht.2⟩) le_rfl)
            (ae_of_all _ fun _ => norm_nonneg _) hi))
  have hfI : Integrable (fun t => ‖f t‖) unitIntervalMeasure := hf.norm.integrableOn_Icc
  have hmean := integral_mono_ae (μ := unitIntervalMeasure) (integrable_const ‖f 0‖)
    (hfI.add (integrable_const (∫ u, ‖d u‖ ∂unitIntervalMeasure)))
    ((ae_restrict_mem measurableSet_Icc).mono hb)
  have hconst : Integrable (fun _ : ℝ => ∫ u, ‖d u‖ ∂unitIntervalMeasure) unitIntervalMeasure :=
    integrable_const _
  change (∫ _ : ℝ, ‖f 0‖ ∂unitIntervalMeasure) ≤
    ∫ t, ‖f t‖ + (∫ u, ‖d u‖ ∂unitIntervalMeasure) ∂unitIntervalMeasure at hmean
  rw [integral_add hfI hconst] at hmean
  simpa only [integral_const, probReal_univ, one_smul] using hmean

private abbrev realCons {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  @Fin.cons n (fun _ => ℝ) t x

private theorem continuous_fin_cons {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X → ℝ} (hx : Continuous x) {v : X → Fin n → ℝ} (hv : Continuous v) :
    Continuous (fun p => realCons (x p) (v p)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · change Continuous (((fun z : Fin n → ℝ => z j) ∘ v))
    exact (continuous_apply j).comp hv

private theorem update_cons_succ {n : ℕ} (t : ℝ) (x : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    update (realCons t x) i.succ u = realCons t (update x i u) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [update_of_ne (Fin.succ_ne_zero i).symm]
    rfl
  · by_cases h : k = i
    · subst k
      simp
    · simp [update_of_ne, h]

private theorem update_cons_zero {n : ℕ} (s t : ℝ) (x : Fin n → ℝ) :
    update (realCons s x) 0 t = realCons t x := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [update_of_ne]

private def cubeConsEquiv (n : ℕ) : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

private theorem cubeConsEquiv_apply {n : ℕ} (a : ℝ × (Fin n → ℝ)) :
    cubeConsEquiv n a = realCons a.1 a.2 := by
  rcases a with ⟨t, x⟩
  simp [cubeConsEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, realCons]

private theorem measurePreserving_cubeConsEquiv (n : ℕ) :
    MeasurePreserving (cubeConsEquiv n) (unitIntervalMeasure.prod (unitDerivativeCube n))
      (unitDerivativeCube (n + 1)) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitIntervalMeasure) 0).symm

private theorem integrable_cube_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (realCons p.1 p.2))
      (unitIntervalMeasure.prod (unitDerivativeCube n)) := by
  have hi := ((measurePreserving_cubeConsEquiv n).integrable_comp_emb
    (cubeConsEquiv n).measurableEmbedding).mpr (continuous_integrable_cube hf)
  have heq : f ∘ cubeConsEquiv n = fun p => f (realCons p.1 p.2) :=
    funext fun p => congrArg f (cubeConsEquiv_apply p)
  exact heq ▸ hi

private theorem integral_cube_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f) :
    (∫ x, ∫ t, f (realCons t x) ∂unitIntervalMeasure ∂unitDerivativeCube n) =
      ∫ u, f u ∂unitDerivativeCube (n + 1) := by
  rw [← (measurePreserving_cubeConsEquiv n).integral_comp' f]
  simp only [cubeConsEquiv_apply]
  exact (integral_prod_symm _ (integrable_cube_cons hf)).symm

/-- A value at the origin of a unit cube is bounded by the sum of the
integrals of the norms of the mixed partial derivatives, using each
coordinate at most once and including the function itself. -/
theorem norm_le_integral_cube_mixedPartials {n : ℕ}
    (D : List (Fin n) → (Fin n → ℝ) → ℂ)
    (hcont : ∀ l, Continuous (D l))
    (hderiv : ∀ l x j t, HasDerivAt (fun u => D l (update x j u))
      (D (j :: l) (update x j t)) t) :
    ‖D [] 0‖ ≤ ((cubeMixedPartials n).map fun l =>
      ∫ u, ‖D l u‖ ∂unitDerivativeCube n).sum := by
  induction n with
  | zero =>
    have h (x : Fin 0 → ℝ) : x = 0 := Subsingleton.elim _ _
    simp only [cubeMixedPartials, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    simp only [h, integral_const, probReal_univ, one_smul, le_refl]
  | succ n ih =>
    let tail (l : List (Fin n)) := l.map Fin.succ
    let D₀ (l : List (Fin n)) (x : Fin n → ℝ) := D (tail l) (realCons 0 x)
    have h₀ : Continuous (fun x : Fin n → ℝ => realCons 0 x) :=
      continuous_fin_cons continuous_const continuous_id
    have hD₀ (l x j t) : HasDerivAt (fun u => D₀ l (update x j u))
        (D₀ (j :: l) (update x j t)) t := by
      simpa only [D₀, tail, List.map_cons, update_cons_succ] using
        hderiv (tail l) (realCons 0 x) j.succ t
    have hI := ih D₀ (fun l => (hcont _).comp h₀) hD₀
    have hz : realCons (0 : ℝ) (0 : Fin n → ℝ) = 0 := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    change ‖D [] (realCons 0 (0 : Fin n → ℝ))‖ ≤ _ at hI
    rw [hz] at hI
    apply hI.trans
    simp only [cubeMixedPartials, List.map_append, List.sum_append, List.map_map]
    rw [← List.sum_map_add]
    apply List.sum_le_sum
    intro l _
    simp only [comp_apply]
    have step (x : Fin n → ℝ) :
        ‖D₀ l x‖ ≤ (∫ t, ‖D (tail l) (realCons t x)‖ ∂unitIntervalMeasure) +
          ∫ t, ‖D (0 :: tail l) (realCons t x)‖ ∂unitIntervalMeasure := by
      refine norm_at_zero_le_integrals ((hcont _).comp
          (continuous_fin_cons continuous_id continuous_const))
        ((hcont _).comp (continuous_fin_cons continuous_id continuous_const)) fun t => ?_
      change HasDerivAt (fun u => D (tail l) (realCons u x))
        (D (0 :: tail l) (realCons t x)) t
      simpa only [update_cons_zero] using hderiv (tail l) (realCons 0 x) 0 t
    have hIn (k : List (Fin (n + 1))) :
        Integrable (fun x : Fin n → ℝ =>
          ∫ t, ‖D k (realCons t x)‖ ∂unitIntervalMeasure) (unitDerivativeCube n) := by
      exact (integrable_cube_cons (hcont k).norm).integral_prod_right
    have hB := integral_mono (continuous_integrable_cube ((hcont (tail l)).comp h₀).norm)
      ((hIn (tail l)).add (hIn (0 :: tail l))) step
    change (∫ x, ‖D₀ l x‖ ∂unitDerivativeCube n) ≤
      ∫ x, (∫ t, ‖D (tail l) (realCons t x)‖ ∂unitIntervalMeasure) +
        (∫ t, ‖D (0 :: tail l) (realCons t x)‖ ∂unitIntervalMeasure) ∂unitDerivativeCube n at hB
    rw [integral_add (hIn (tail l)) (hIn (0 :: tail l)), integral_cube_cons (hcont (tail l)).norm,
      integral_cube_cons (hcont (0 :: tail l)).norm] at hB
    exact hB

/-- The cube estimate transported to an affine chart. A fixed list of
directions may be differentiated before taking the additional mixed partials. -/
theorem norm_listDerivative_le_integral_affineCube {n : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (A : (Fin n → ℝ) →L[ℝ] X)
    (b : X) {f : X → ℂ} (hf : ContDiff ℝ ∞ f) (v : List X) :
    ‖listDerivative f v b‖ ≤ ((cubeMixedPartials n).map fun l =>
      ∫ u, ‖listDerivative f (l.map (fun j => A (Pi.single j 1)) ++ v) (b + A u)‖
        ∂unitDerivativeCube n).sum := by
  let D (l : List (Fin n)) (u : Fin n → ℝ) :=
    listDerivative f (l.map (fun j => A (Pi.single j 1)) ++ v) (b + A u)
  have hcont (l : List (Fin n)) : Continuous (D l) :=
    (listDerivative_continuous hf _).comp (continuous_const.add A.continuous)
  have hderiv (l : List (Fin n)) (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
      HasDerivAt (fun u => D l (update x j u)) (D (j :: l) (update x j t)) t :=
    hasDerivAt_listDerivative hf _ (cube_affine_update A b x j t)
  simpa only [D, List.map_nil, List.nil_append, map_zero, add_zero] using
    norm_le_integral_cube_mixedPartials D hcont hderiv

theorem unitDerivativeCube_le_volume (n : ℕ) : unitDerivativeCube n ≤ volume := by
  rw [unitDerivativeCube, ← Measure.restrict_pi_pi]
  exact Measure.restrict_le_self

theorem aes_unitDerivativeCube_mem (n : ℕ) :
    ∀ᵐ u ∂unitDerivativeCube n, ∀ j, u j ∈ Icc (0 : ℝ) 1 := by
  rw [unitDerivativeCube, ← Measure.restrict_pi_pi]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).mono
    (fun _ h j => h j (mem_univ j))

/-- If the image of the unit cube is dominated by a reference measure, the
cube integral is bounded by the global Lᵖ norm for every exponent at least one. -/
theorem integral_norm_cube_le_lpNorm_of_map_le {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : (Fin n → ℝ) → Y} (hT : Measurable T)
    (hmap : Measure.map T (unitDerivativeCube n) ≤ μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Y → ℂ} (hg : MemLp g p μ) :
    (∫ u, ‖g (T u)‖ ∂unitDerivativeCube n) ≤ lpNorm g p μ := by
  have hg' := hg.mono_measure hmap
  have hcomp := hg'.comp_of_map hT.aemeasurable
  change (∫ u, ‖(g ∘ T) u‖ ∂unitDerivativeCube n) ≤ lpNorm g p μ
  rw [← lpNorm_one_eq_integral_norm hcomp.aestronglyMeasurable,
    ← toReal_eLpNorm hcomp.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable]
  apply ENNReal.toReal_mono hg.eLpNorm_lt_top.ne
  calc
    _ ≤ eLpNorm (g ∘ T) p (unitDerivativeCube n) :=
      eLpNorm_le_eLpNorm_of_exponent_le hp hcomp.aestronglyMeasurable
    _ = eLpNorm g p (Measure.map T (unitDerivativeCube n)) :=
      (eLpNorm_map_measure hg'.aestronglyMeasurable hT.aemeasurable).symm
    _ ≤ _ := eLpNorm_mono_measure g hmap

/-- The Euclidean supremum-to-Lᵖ comparison in standard coordinates. The
bound is uniform in the base point and uses only the additional mixed partials. -/
theorem norm_listDerivative_le_euclidean_lpNorm {n : ℕ}
    {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (v : List (Fin n → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hLp : ∀ l ∈ cubeMixedPartials n, MemLp
      (listDerivative f (l.map (fun j => Pi.single j 1) ++ v)) p volume) (b : Fin n → ℝ) :
    ‖listDerivative f v b‖ ≤ ((cubeMixedPartials n).map fun l =>
      lpNorm (listDerivative f (l.map (fun j => Pi.single j 1) ++ v)) p volume).sum := by
  have hT : Measurable (fun u : Fin n → ℝ => b + u) := (continuous_const.add continuous_id).measurable
  have hmap : Measure.map (fun u : Fin n → ℝ => b + u) (unitDerivativeCube n) ≤ volume :=
    (Measure.map_mono (unitDerivativeCube_le_volume n) hT).trans_eq
      (measurePreserving_add_left volume b).map_eq
  refine (norm_listDerivative_le_integral_affineCube
    (ContinuousLinearMap.id ℝ (Fin n → ℝ)) b hf v).trans ?_
  apply List.sum_le_sum
  intro l hl
  exact integral_norm_cube_le_lpNorm_of_map_le hT hmap hp (hLp l hl)

/-- A translated unit cube maps to normalized Haar measure on the product
of unit circles. Cube boundaries have measure zero. -/
theorem measurePreserving_unitDerivativeCube_torus {n : ℕ} (b : Fin n → ℝ) :
    MeasurePreserving (fun u : Fin n → ℝ => fun j => ((b j + u j : ℝ) : AddCircle (1 : ℝ)))
      (unitDerivativeCube n) (volume : Measure (Fin n → AddCircle (1 : ℝ))) := by
  have h0 : MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) unitIntervalMeasure volume := by
    have he : volume.restrict (Ioc (0 : ℝ) 1) = unitIntervalMeasure :=
      Measure.restrict_congr_set Ioc_ae_eq_Icc
    simpa only [zero_add, he] using (AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0)
  have h (j : Fin n) : MeasurePreserving (fun u : ℝ => ((b j + u : ℝ) : AddCircle (1 : ℝ)))
      unitIntervalMeasure volume := by
    simp only [AddCircle.coe_add]
    change MeasurePreserving ((fun z : AddCircle (1 : ℝ) => (b j : AddCircle (1 : ℝ)) + z) ∘
      ((↑) : ℝ → AddCircle (1 : ℝ))) unitIntervalMeasure volume
    exact (measurePreserving_add_left volume (b j : AddCircle (1 : ℝ))).comp h0
  exact measurePreserving_pi _ _ h

/-- The finite Lᵖ estimate on the torus for derivatives that descend from its
Euclidean cover. The norm on the right uses the actual circle Haar measures. -/
theorem norm_listDerivative_le_torus_lpNorm {n : ℕ}
    {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (v : List (Fin n → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (g : List (Fin n) → (Fin n → AddCircle (1 : ℝ)) → ℂ)
    (hrep : ∀ l ∈ cubeMixedPartials n, ∀ x,
      listDerivative f (l.map (fun j => Pi.single j 1) ++ v) x =
        g l (fun j => (x j : AddCircle (1 : ℝ))))
    (hLp : ∀ l ∈ cubeMixedPartials n, MemLp (g l) p volume) (b : Fin n → ℝ) :
    ‖listDerivative f v b‖ ≤ ((cubeMixedPartials n).map fun l => lpNorm (g l) p volume).sum := by
  let T (u : Fin n → ℝ) (j : Fin n) : AddCircle (1 : ℝ) := ((b j + u j : ℝ) : AddCircle (1 : ℝ))
  have hT : MeasurePreserving T (unitDerivativeCube n) volume :=
    measurePreserving_unitDerivativeCube_torus b
  refine (norm_listDerivative_le_integral_affineCube
    (ContinuousLinearMap.id ℝ (Fin n → ℝ)) b hf v).trans ?_
  apply List.sum_le_sum
  intro l hl
  have he (u : Fin n → ℝ) :
      listDerivative f (l.map (fun j => Pi.single j 1) ++ v) (b + u) = g l (T u) :=
    hrep l hl (b + u)
  change (∫ u, ‖listDerivative f (l.map (fun j => Pi.single j 1) ++ v) (b + u)‖
    ∂unitDerivativeCube n) ≤ lpNorm (g l) p volume
  simp only [he]
  exact integral_norm_cube_le_lpNorm_of_map_le hT.measurable hT.map_eq.le hp (hLp l hl)

/-- Standard covering projection with the real coordinates left unquotiented. -/
def realTorusProjection {m n : ℕ} (x : Fin (m + n) → ℝ) :
    (Fin m → ℝ) × (Fin n → AddCircle (1 : ℝ)) :=
  (fun i => x (Fin.castAdd n i), fun j => (x (Fin.natAdd m j) : AddCircle (1 : ℝ)))

/-- On the product of the real vector and torus factors the image of any
translated cube is dominated by the product of Lebesgue and Haar measures. -/
theorem realTorusProjection_map_cube_le {m n : ℕ} (b : Fin (m + n) → ℝ) :
    Measure.map (fun x => realTorusProjection (m := m) (n := n) (b + x))
        (unitDerivativeCube (m + n)) ≤
      (volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin n → AddCircle (1 : ℝ))) := by
  let R (u : Fin m → ℝ) (i : Fin m) := b (Fin.castAdd n i) + u i
  let T (u : Fin n → ℝ) (j : Fin n) : AddCircle (1 : ℝ) :=
    ((b (Fin.natAdd m j) + u j : ℝ) : AddCircle (1 : ℝ))
  let split (u : Fin (m + n) → ℝ) : (Fin m → ℝ) × (Fin n → ℝ) :=
    (fun i => u (Fin.castAdd n i), fun j => u (Fin.natAdd m j))
  have hsplit : MeasurePreserving split (unitDerivativeCube (m + n))
      ((unitDerivativeCube m).prod (unitDerivativeCube n)) := by
    let e := MeasurableEquiv.piCongrLeft (fun _ : Fin m ⊕ Fin n => ℝ)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm
    have he : MeasurePreserving e (unitDerivativeCube (m + n))
        (Measure.pi fun _ : Fin m ⊕ Fin n => unitIntervalMeasure) :=
      measurePreserving_piCongrLeft (fun _ : Fin m ⊕ Fin n => unitIntervalMeasure)
        (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm
    let d := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)
    have hd : MeasurePreserving d (Measure.pi fun _ : Fin m ⊕ Fin n => unitIntervalMeasure)
        ((unitDerivativeCube m).prod (unitDerivativeCube n)) :=
      measurePreserving_sumPiEquivProdPi fun _ => unitIntervalMeasure
    have hs : split = d ∘ e := by
      funext u
      apply Prod.ext
      · funext i
        change u (Fin.castAdd n i) = e u (.inl i)
        simpa only [e, finSumFinEquiv_symm_apply_castAdd] using
          (MeasurableEquiv.piCongrLeft_apply_apply
            (β := fun _ : Fin m ⊕ Fin n => ℝ)
            (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm u (Fin.castAdd n i)).symm
      · funext j
        change u (Fin.natAdd m j) = e u (.inr j)
        simpa only [e, finSumFinEquiv_symm_apply_natAdd] using
          (MeasurableEquiv.piCongrLeft_apply_apply
            (β := fun _ : Fin m ⊕ Fin n => ℝ)
            (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm u (Fin.natAdd m j)).symm
    rw [hs]
    exact hd.comp he
  have hR₀ : MeasurePreserving R volume volume :=
    measurePreserving_add_left volume (fun i : Fin m => b (Fin.castAdd n i))
  have hR : Measure.map R (unitDerivativeCube m) ≤ volume :=
    (Measure.map_mono (unitDerivativeCube_le_volume m) hR₀.measurable).trans_eq hR₀.map_eq
  have hT : MeasurePreserving T (unitDerivativeCube n) volume :=
    measurePreserving_unitDerivativeCube_torus (fun j : Fin n => b (Fin.natAdd m j))
  change Measure.map (Prod.map R T ∘ split) (unitDerivativeCube (m + n)) ≤ _
  rw [← Measure.map_map (hR₀.measurable.prodMap hT.measurable) hsplit.measurable,
    hsplit.map_eq, ← Measure.map_prod_map _ _ hR₀.measurable hT.measurable, hT.map_eq]
  exact Measure.prod_mono hR le_rfl

theorem dirac_le_count {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (a : A) : Measure.dirac a ≤ Measure.count := by
  refine Measure.le_iff.mpr fun s hs => ?_
  by_cases h : a ∈ s
  · rw [Measure.dirac_apply_of_mem h, ← Measure.count_singleton a]
    exact measure_mono (singleton_subset_iff.mpr h)
  · rw [Measure.dirac_apply' _ hs, indicator_of_notMem h]
    exact bot_le


theorem realTorusProjection_measurable {m n : ℕ} :
    Measurable (realTorusProjection (m := m) (n := n)) := by
  exact (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_lambda _ fun _ => AddCircle.measurable_mk'.comp (measurable_pi_apply _))

/-- A fixed discrete slice adds a Dirac factor to the image measure. -/
theorem realTorusProjection_map_cube_discrete_le {m n : ℕ} {A : Type*} [MeasurableSpace A]
    (b : Fin (m + n) → ℝ) (a : A) {ν : Measure A} [SFinite ν] (ha : Measure.dirac a ≤ ν) :
    Measure.map (fun u => (realTorusProjection (m := m) (n := n) (b + u), a))
      (unitDerivativeCube (m + n)) ≤ (((volume : Measure (Fin m → ℝ)).prod volume).prod ν) := by
  let T (u : Fin (m + n) → ℝ) := realTorusProjection (m := m) (n := n) (b + u)
  have hT : Measurable T :=
    realTorusProjection_measurable.comp (continuous_const.add continuous_id).measurable
  have hm : Measurable (fun y : (Fin m → ℝ) × (Fin n → AddCircle (1 : ℝ)) => (y, a)) :=
    measurable_id.prodMk measurable_const
  change Measure.map ((fun y => (y, a)) ∘ T) (unitDerivativeCube (m + n)) ≤ _
  rw [← Measure.map_map hm hT, ← Measure.prod_dirac]
  exact Measure.prod_mono (realTorusProjection_map_cube_le (m := m) (n := n) b) ha

/-- Pointwise mixed derivatives on a slice of a real-vector, torus and
countable discrete product are bounded by global Lᵖ norms. The reference
measure is Lebesgue measure, torus Haar measure, and counting measure. -/
theorem norm_listDerivative_le_realTorus_discrete_lpNorm {m n : ℕ} {A : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    {f : (Fin (m + n) → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (v : List (Fin (m + n) → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (a : A)
    (g : List (Fin (m + n)) → (((Fin m → ℝ) × (Fin n → AddCircle (1 : ℝ))) × A) → ℂ)
    (hrep : ∀ l ∈ cubeMixedPartials (m + n), ∀ x,
      listDerivative f (l.map (fun j => Pi.single j 1) ++ v) x = g l (realTorusProjection x, a))
    (hLp : ∀ l ∈ cubeMixedPartials (m + n),
      MemLp (g l) p (((volume : Measure (Fin m → ℝ)).prod volume).prod Measure.count))
    (b : Fin (m + n) → ℝ) :
    ‖listDerivative f v b‖ ≤ ((cubeMixedPartials (m + n)).map fun l =>
      lpNorm (g l) p (((volume : Measure (Fin m → ℝ)).prod volume).prod Measure.count)).sum := by
  let T (u : Fin (m + n) → ℝ) := realTorusProjection (m := m) (n := n) (b + u)
  have hT : Measurable T :=
    realTorusProjection_measurable.comp (continuous_const.add continuous_id).measurable
  have hmaps := realTorusProjection_map_cube_discrete_le (m := m) (n := n) b a (dirac_le_count a)
  refine (norm_listDerivative_le_integral_affineCube
    (ContinuousLinearMap.id ℝ (Fin (m + n) → ℝ)) b hf v).trans ?_
  apply List.sum_le_sum
  intro l hl
  change (∫ u, ‖listDerivative f (l.map (fun j => Pi.single j 1) ++ v) (b + u)‖
    ∂unitDerivativeCube (m + n)) ≤ _
  simp only [hrep l hl]
  exact integral_norm_cube_le_lpNorm_of_map_le (hT.prodMk measurable_const) hmaps hp (hLp l hl)

end
end Masullo
