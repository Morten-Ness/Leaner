import Mathlib

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i}

theorem IsUnit.val_inv_apply (hx : IsUnit x) (i : ι) : (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹ := by
  rw [← Units.inv_eq_val_inv, ← MulEquiv.val_inv_piUnits_apply]; congr; ext; rfl

