import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

open Bornology Filter Function Set Topology
open scoped PointwiseConvergenceCLM

namespace Masullo

noncomputable section

universe u v

variable {E : Type u} {F : ℕ → Type v}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)] [∀ n, TopologicalSpace (F n)]

/-- An increasing inductive presentation, with the continuous maps into the
limit kept separate from the intrinsic topology of each stage. -/
structure LinearInductivePresentation (E : Type u) (F : ℕ → Type v)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)] [∀ n, TopologicalSpace (F n)] where
  incl (n : ℕ) : F n →L[ℂ] E
  transition {m n : ℕ} (h : m ≤ n) : F m →L[ℂ] F n
  injective_incl (n : ℕ) : Injective (incl n)
  incl_transition {m n : ℕ} (h : m ≤ n) (x : F m) : incl n (transition h x) = incl m x
  exhaust (x : E) : ∃ n, x ∈ range (incl n)
  continuous_limit (l : E →ₗ[ℂ] ℂ) : Continuous l ↔ ∀ n, Continuous (l.comp (incl n).toLinearMap)

namespace LinearInductivePresentation

variable (D : LinearInductivePresentation E F)

def CompatibleDual : Submodule ℂ (∀ n, StrongDual ℂ (F n)) where
  carrier := {g | ∀ (m n : ℕ) (h : m ≤ n) (x : F m), g n (D.transition h x) = g m x}
  zero_mem' := by intro; simp
  add_mem' := by
    intro a b ha hb m n h x
    change a n (D.transition h x) + b n (D.transition h x) = a m x + b m x
    rw [ha m n h, hb m n h]
  smul_mem' := by
    intro c a ha m n h x
    change c • a n (D.transition h x) = c • a m x
    rw [ha m n h]

section Descent

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
variable (g : ∀ n, F n →ₗ[ℂ] Y)
variable (hg : ∀ m n (h : m ≤ n) (x : F m), g n (D.transition h x) = g m x)

include hg in
private theorem compatible_values {m n : ℕ}
    (x : F m) (y : F n) (h : D.incl m x = D.incl n y) :
    g m x = g n y := by
  let k := max m n
  have he : D.transition (le_max_left m n) x = D.transition (le_max_right m n) y := by
    apply D.injective_incl k
    exact (D.incl_transition (le_max_left m n) x).trans (h.trans
      (D.incl_transition (le_max_right m n) y).symm)
  exact (hg m k (le_max_left m n) x).symm.trans
    ((congrArg (g k) he).trans (hg n k (le_max_right m n) y))

private def descFun (x : E) : Y :=
  let n := (D.exhaust x).choose
  g n ((D.exhaust x).choose_spec.choose)

include hg in
private theorem descFun_incl (n : ℕ) (x : F n) :
    D.descFun g (D.incl n x) = g n x := by
  unfold descFun
  exact D.compatible_values g hg _ _ (D.exhaust _).choose_spec.choose_spec

/-- Compatible linear maps on the stages give a linear map on the union. -/
def linearMapOfCompatible : E →ₗ[ℂ] Y where
  toFun := D.descFun g
  map_add' x y := by
    obtain ⟨m, a, rfl⟩ := D.exhaust x
    obtain ⟨n, b, rfl⟩ := D.exhaust y
    let k := max m n
    let a' := D.transition (le_max_left m n) a
    let b' := D.transition (le_max_right m n) b
    change D.descFun g (D.incl m a + D.incl n b) =
      D.descFun g (D.incl m a) + D.descFun g (D.incl n b)
    rw [← D.incl_transition (le_max_left m n) a, ← D.incl_transition (le_max_right m n) b]
    change D.descFun g (D.incl k a' + D.incl k b') = D.descFun g (D.incl k a') + D.descFun g (D.incl k b')
    have he : D.descFun g (D.incl k a' + D.incl k b') =
        D.descFun g (D.incl k (a' + b')) :=
      congrArg (D.descFun g) ((D.incl k).map_add _ _).symm
    rw [he, D.descFun_incl g hg, D.descFun_incl g hg, D.descFun_incl g hg, map_add]
  map_smul' c x := by
    obtain ⟨n, a, rfl⟩ := D.exhaust x
    change D.descFun g (c • D.incl n a) = c • D.descFun g (D.incl n a)
    rw [← map_smul, D.descFun_incl g hg, D.descFun_incl g hg, map_smul]

@[simp]
theorem linearMapOfCompatible_incl (n : ℕ) (x : F n) :
    D.linearMapOfCompatible g hg (D.incl n x) = g n x :=
  D.descFun_incl g hg n x

end Descent

private def desc (g : D.CompatibleDual) : StrongDual ℂ E := by
  let L := D.linearMapOfCompatible (fun n => (g.val n).toLinearMap) g.property
  refine ⟨L, (D.continuous_limit L).mpr ?_⟩
  intro n
  have he : L.comp (D.incl n).toLinearMap = (g.val n).toLinearMap :=
    LinearMap.ext (D.linearMapOfCompatible_incl (fun n => (g.val n).toLinearMap) g.property n)
  rw [he]
  exact (g.val n).continuous

/-- Restriction identifies the linear dual of the inductive limit with
compatible families of continuous linear forms on the stages. -/
def dualRestriction : StrongDual ℂ E ≃ₗ[ℂ] D.CompatibleDual := by
  let L : StrongDual ℂ E →ₗ[ℂ] D.CompatibleDual :=
    { toFun := fun g => ⟨fun n => g.comp (D.incl n), fun m n h x =>
        congrArg g (D.incl_transition h x)⟩
      map_add' := fun a b => Subtype.ext (funext fun n => ContinuousLinearMap.ext fun _ => rfl)
      map_smul' := fun c a => Subtype.ext (funext fun n => ContinuousLinearMap.ext fun _ => rfl) }
  apply LinearEquiv.ofBijective L
  constructor
  · intro a b h
    ext x
    obtain ⟨n, y, rfl⟩ := D.exhaust x
    exact congrArg (fun w : D.CompatibleDual => w.val n y) h
  · intro g
    exact ⟨D.desc g, Subtype.ext (funext fun n => ContinuousLinearMap.ext (D.linearMapOfCompatible_incl (fun k => (g.val k).toLinearMap) g.property n))⟩

@[simp] theorem dualRestriction_apply (g : StrongDual ℂ E) (n : ℕ) (x : F n) :
    (D.dualRestriction g).val n x = g (D.incl n x) := rfl

private theorem dualRestriction_inverse_eval (g : D.CompatibleDual) (n : ℕ) (x : F n) :
    D.dualRestriction.symm g (D.incl n x) = g.val n x := by
  rw [← dualRestriction_apply, LinearEquiv.apply_symm_apply]

/-- Compatible weak duals carry the projective-limit topology, induced from
the product of the pointwise convergence topologies on the stages. -/
def WeakCompatibleDual := D.CompatibleDual

instance : AddCommGroup D.WeakCompatibleDual :=
  inferInstanceAs (AddCommGroup D.CompatibleDual)

instance : Module ℂ D.WeakCompatibleDual := inferInstanceAs (Module ℂ D.CompatibleDual)

private def weakCoordinates (g : D.WeakCompatibleDual) : ∀ n, F n →Lₚₜ[ℂ] ℂ :=
  fun n => (show D.CompatibleDual from g).val n

instance : TopologicalSpace D.WeakCompatibleDual :=
  TopologicalSpace.induced D.weakCoordinates inferInstance

/-- The weak-dual isomorphism for a locally convex inductive limit. -/
def weakDualRestriction : (E →Lₚₜ[ℂ] ℂ) ≃L[ℂ] D.WeakCompatibleDual where
  toLinearEquiv := D.dualRestriction
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro n
    exact (PointwiseConvergenceCLM.precomp ℂ (D.incl n) :
      (E →Lₚₜ[ℂ] ℂ) →L[ℂ] (F n →Lₚₜ[ℂ] ℂ)).continuous
  continuous_invFun := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro x
    obtain ⟨n, y, rfl⟩ := D.exhaust x
    have hc : Continuous D.weakCoordinates := continuous_induced_dom
    have he : Continuous (fun d : D.WeakCompatibleDual => D.weakCoordinates d n y) :=
      ((continuous_apply y).comp
        (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) (F n) ℂ).continuous).comp
        ((continuous_apply n).comp hc)
    convert he using 1
    funext g
    exact D.dualRestriction_inverse_eval g n y

/-- Bounded sets that come from bounded sets of stages give the corresponding
isomorphism for the strong dual topologies. -/
def strongDualRestriction (hBounded : ∀ B : Set E, IsVonNBounded ℂ B →
    ∃ (n : ℕ) (C : Set (F n)), IsVonNBounded ℂ C ∧ B ⊆ D.incl n '' C) :
    StrongDual ℂ E ≃L[ℂ] D.CompatibleDual where
  toLinearEquiv := D.dualRestriction
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro n
    exact (ContinuousLinearMap.precomp ℂ (D.incl n) :
      (StrongDual ℂ E) →L[ℂ] StrongDual ℂ (F n)).continuous
  continuous_invFun := by
    change Continuous (D.dualRestriction.symm.toLinearMap.toAddMonoidHom :
      D.CompatibleDual → StrongDual ℂ E)
    refine continuous_of_tendsto_nhds_zero (G := D.CompatibleDual) (M := StrongDual ℂ E)
      D.dualRestriction.symm.toLinearMap.toAddMonoidHom ?_
    rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
    rintro ⟨B, V⟩ ⟨hB, hV⟩
    obtain ⟨n, C, hC, hBC⟩ := hBounded B hB
    have hV' : {f : StrongDual ℂ (F n) | ∀ x ∈ C, f x ∈ V} ∈ 𝓝 0 :=
      ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem (i := (C, V)) ⟨hC, hV⟩
    have hc : Continuous (fun g : D.CompatibleDual => g.val n) :=
      (continuous_apply n).comp continuous_subtype_val
    have ht : Tendsto (fun g : D.CompatibleDual => g.val n) (𝓝 0) (𝓝 0) :=
      hc.tendsto 0
    have h := ht.eventually hV'
    filter_upwards [h] with g hg x hx
    obtain ⟨y, hy, rfl⟩ := hBC hx
    change D.dualRestriction.symm g (D.incl n y) ∈ V
    rw [D.dualRestriction_inverse_eval]
    exact hg y hy

end LinearInductivePresentation

end

end Masullo
