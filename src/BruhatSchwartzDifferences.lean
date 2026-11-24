import BruhatSchwartzTranslation
import Mathlib.Topology.Algebra.PontryaginDual

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The cyclic difference in (4.6.1.4) on the actual Schwartz–Bruhat space. -/
def bruhatSchwartzDifference (g : G) : BruhatSchwartz G →L[ℂ] BruhatSchwartz G :=
  ContinuousLinearMap.id ℂ _ - bruhatSchwartz_translate g⁻¹

@[simp] theorem bruhatSchwartzDifference_apply
    (g : G) (f : BruhatSchwartz G) (x : G) :
    (bruhatSchwartzDifference g f).val x = f.val x - f.val (g * x) := by
  change f.val x - (bruhatSchwartz_translate g⁻¹ f).val x = _
  rw [bruhatSchwartz_translate_apply, inv_inv]

/-- Successive cyclic differences, with repeated generators retained. -/
def bruhatSchwartzDifferenceProduct : List G → BruhatSchwartz G →L[ℂ] BruhatSchwartz G
  | [] => ContinuousLinearMap.id ℂ _
  | g :: gs => (bruhatSchwartzDifference g).comp (bruhatSchwartzDifferenceProduct gs)

/-- The pointwise repeated-generator formula in §4.6. -/
theorem bruhatSchwartzDifferenceProduct_pair_apply (g : G) (f : BruhatSchwartz G) (x : G) :
    (bruhatSchwartzDifferenceProduct [g, g] f).val x =
      f.val x - 2 * f.val (g * x) + f.val (g ^ 2 * x) := by
  simp [bruhatSchwartzDifferenceProduct, pow_two, mul_assoc]
  ring

/-- A difference product preserves the character isotype of any subgroup,
including the norm-one subgroup. Adapted from mccorvie/riemann-masullo,
commit add4562. -/
theorem bruhatSchwartzDifferenceProduct_preserves_isotype {H : Subgroup G}
    (χ : PontryaginDual H) (gs : List G) (f : BruhatSchwartz G)
    (hf : ∀ (h : H) x, f.val (h.val⁻¹ * x) = (χ h : ℂ) * f.val x) :
    ∀ (h : H) x, (bruhatSchwartzDifferenceProduct gs f).val (h.val⁻¹ * x) =
      (χ h : ℂ) * (bruhatSchwartzDifferenceProduct gs f).val x := by
  induction gs with
  | nil => exact hf
  | cons g gs ih =>
    intro h x
    let u := bruhatSchwartzDifferenceProduct gs f
    change (bruhatSchwartzDifference g u).val (h.val⁻¹ * x) =
      (χ h : ℂ) * (bruhatSchwartzDifference g u).val x
    have hu (y : G) : u.val (h.val⁻¹ * y) = (χ h : ℂ) * u.val y := ih h y
    rw [bruhatSchwartzDifference_apply, bruhatSchwartzDifference_apply,
      mul_left_comm g, hu, hu, mul_sub]

end

end Masullo
