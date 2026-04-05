import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R]

theorem noZeroDivisors_iff : NoZeroDivisors R[X] ↔ NoZeroDivisors R where
  mp _ := Polynomial.C_injective.noZeroDivisors _ Polynomial.C_0 fun _ _ ↦ Polynomial.C_mul
  mpr _ := inferInstance

