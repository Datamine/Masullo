import ElementaryCyclicTails
import BruhatCompactSupport

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

variable {m n r m' n' r' : ℕ} {F F' : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']

local notation "A" => ElementaryLCAModel m n r F
local notation "B" => ElementaryLCAModel m' n' r' F'
local notation "S" => ElementarySchwartz m n r F

/-- Cyclic orbit sums on an elementary chart descend to a Schwartz test
on any compact elementary quotient with that cyclic kernel. -/
theorem exists_elementaryCyclicPeriodization
    (l : A →+ ℝ) (hl : Continuous l) (s : A) (hs : 0 < l s)
    (φ : A →+ B) (hφ : Continuous φ) (ho : IsOpenMap φ) (hS : Surjective φ)
    (hker : ∀ x, φ x = 0 ↔ ∃ j : ℤ, j • s = x) (hc : IsCompact (univ : Set B))
    (f : S) :
    ∃ g : ElementarySchwartz m' n' r' F', ∀ x, g (φ x) = ∑' j : ℤ, f (x + j • s) := by
  let u (x : A) := ∑' j : ℤ, f (x + j • s)
  have hu (a : Fin r → ℤ) (b : F) :
      ContDiff ℝ ∞ (fun x ↦ u (elementaryCover x a b)) :=
    (elementaryCyclicSeries_smooth id injective_id l hl s hs f a b).1
  have hInv {x y : A} (he : φ x = φ y) : u x = u y := by
    have h₀ : φ (x - y) = 0 := by rw [map_sub, he, sub_self]
    obtain ⟨k, hk⟩ := (hker _).1 h₀
    have hx : x = y + k • s := by rw [hk, add_sub_cancel]
    dsimp only [u]
    conv_lhs => rw [hx]
    have heq (j : ℤ) : y + k • s + j • s = y + (j + k) • s := by
      rw [add_zsmul]
      ac_rfl
    simp_rw [heq]
    exact (Equiv.addRight k).tsum_eq (fun j : ℤ ↦ f (y + j • s))
  obtain ⟨σ, hσ⟩ := hS.hasRightInverse
  let g := u ∘ σ
  have hEq : g ∘ φ = u := by
    funext x
    exact hInv (hσ (φ x))
  have hG := elementaryContDiff_of_open φ hφ ho u g hu hEq
    (fun y hy ↦ (hy (hS y)).elim)
  have hcG : HasCompactSupport g := HasCompactSupport.intro' hc isClosed_univ (by simp)
  exact ⟨⟨g, elementarySchwartz_mem_of_compactSupport g hcG hG⟩, fun x ↦ congrFun hEq x⟩

/-- A compact logarithmic cutoff makes the pullback of an elementary
quotient test a Schwartz function, even if the quotient map is nonproper. -/
theorem elementarySchwartz_logCutoff_pullback_mem
    (l : A →+ ℝ) (hl : IsProperMap l) (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (K : Set ℝ) (hK : IsCompact K) (hs : support b ⊆ K)
    (φ : A →+ B) (hφ : Continuous φ) (f : ElementarySchwartz m' n' r' F') :
    (fun x : A ↦ b (l x) * f (φ x)) ∈ elementarySchwartzSubmodule m n r F := by
  let g (x : A) := b (l x) * f (φ x)
  have hc : HasCompactSupport g := HasCompactSupport.intro'
    (hl.isCompact_preimage hK) (hK.isClosed.preimage hl.continuous) fun x hx ↦ by
      have hzero : b (l x) = 0 := by
        by_contra h
        exact hx (hs h)
      simp [g, hzero]
  refine elementarySchwartz_mem_of_compactSupport g hc fun a c ↦ ?_
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let H := l.comp (elementaryCoverHom : X →+ A)
  have hH : Continuous H := hl.continuous.comp elementaryCoverHom_continuous
  let L := H.toRealLinearMap hH
  have hlog (x : X) : l (elementaryCover x a c) = L x + l (elementaryCover (0 : X) a c) := by
    have he := elementaryCover_add (0 : X) x a c
    rw [zero_add] at he
    rw [he, map_add, add_comm]
    rfl
  obtain ⟨T, hT⟩ := elementaryCover_hom_affine φ hφ
  obtain ⟨y, a', c', he⟩ := hT a c
  have hg : (fun x : X ↦ g (elementaryCover x a c)) =
      fun x : X ↦ b (L x + l (elementaryCover (0 : X) a c)) * f (elementaryCover (T x + y) a' c') := by
    funext x
    change b (l (elementaryCover x a c)) * f (φ (elementaryCover x a c)) = _
    rw [hlog, he]
  rw [hg]
  exact (hb.comp (L.contDiff.add contDiff_const)).mul
    ((f.property.1 a' c').comp (T.contDiff.add contDiff_const))

end

end Masullo
