import Mathlib

section

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i}

theorem IsUnit.val_inv_apply (hx : IsUnit x) (i : ι) : (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹ := by
  rw [← Units.inv_eq_val_inv, ← MulEquiv.val_inv_piUnits_apply]; congr; ext; rfl

end

section

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i}

theorem Pi.isUnit_iff :
    IsUnit x ↔ ∀ i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y ↦ x i * y = 1 ∧ y * x i = 1).symm

end
