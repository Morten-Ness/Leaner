import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_range {ι : Sort*} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← Set.image_inv_eq_inv]
  exact (range_comp ..).symm

