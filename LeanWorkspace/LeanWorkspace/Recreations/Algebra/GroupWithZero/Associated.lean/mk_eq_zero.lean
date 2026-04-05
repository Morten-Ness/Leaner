import Mathlib

variable {M : Type*}

variable [MonoidWithZero M]

theorem mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0 := ⟨fun h => (associated_zero_iff_eq_zero a).1 <| Quotient.exact h, fun h => Associated.symm h ▸ Associated.rfl⟩

