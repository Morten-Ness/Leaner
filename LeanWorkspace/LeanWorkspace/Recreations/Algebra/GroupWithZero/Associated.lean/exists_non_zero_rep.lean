import Mathlib

variable {M : Type*}

variable [MonoidWithZero M]

theorem exists_non_zero_rep {a : Associates M} : a ≠ 0 → ∃ a0 : M, a0 ≠ 0 ∧ Associates.mk a0 = a := Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk'') nz, Associated.rfl⟩

