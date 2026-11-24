import CompactFamilySchwartz
import ModulatedExponentialRadial

open Filter Function Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker
local notation "S" => BruhatSchwartz G

include hτ in
set_option maxHeartbeats 1200000 in
/-- Split a genuine Bruhat test into a radial Schwartz function valued in the
supremum norm on the compact kernel. All radial seminorms are continuous
in the original locally convex inductive limit topology. -/
theorem exists_bruhatSplitSchwartz :
    ∃ L : S →L[ℂ] 𝓢(ℝ, C(K, ℂ)),
      ∀ (f : S) (x : ℝ) (k : K), L f x k = f.val (τ (Multiplicative.ofAdd x) * k.val) := by
  let R := bruhatSchwartz_radialRestriction τ hτ
  let A (k : K) (f : S) := R (bruhatSchwartz_translate k.val⁻¹ f)
  have hA : Continuous (fun z : K × S ↦ A z.1 z.2) :=
    R.continuous.comp (continuous_bruhatSchwartz_translate.comp
      (((continuous_subtype_val.comp continuous_fst).inv).prodMk continuous_snd))
  have hAeval (f : S) (x : ℝ) (k : K) : A k f x =
      f.val (τ (Multiplicative.ofAdd x) * k.val) := by
    dsimp only [A, R]
    rw [bruhatSchwartz_radialRestriction_apply, bruhatSchwartz_translate_apply, inv_inv, mul_comm]
  let B (k : K) : S →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
    (R.comp (bruhatSchwartz_translate k.val⁻¹)).toLinearMap
  obtain ⟨L, hL⟩ := exists_continuous_compactFamilySchwartz B hA
  exact ⟨L, fun f x k ↦ (hL f x k).trans (hAeval f x k)⟩

end
end Masullo
