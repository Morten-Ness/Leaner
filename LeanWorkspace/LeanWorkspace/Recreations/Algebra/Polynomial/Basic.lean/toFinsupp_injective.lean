import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X] → AddMonoidAlgebra _ _) := fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

