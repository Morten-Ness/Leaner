import Mathlib

variable {A M G α β γ : Type*}

theorem eq_inv_iff_eq {f : Equiv.Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y := f.eq_symm_apply

