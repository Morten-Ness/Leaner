import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

theorem mk_one_mul_mk_one [Mul M] [MulOneClass N] (a₁ a₂ : M) :
    (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) := by
  rw [mk_mul_mk, mul_one]

