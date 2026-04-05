import Mathlib

variable {A M G α β γ : Type*}

theorem inv_eq_iff_eq {f : Equiv.Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y := f.symm_apply_eq

