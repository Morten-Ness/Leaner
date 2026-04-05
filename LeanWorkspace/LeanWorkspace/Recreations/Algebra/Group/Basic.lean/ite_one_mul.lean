import Mathlib

variable {α β G M : Type*}

variable [MulOneClass M]

theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h : P <;> simp [h]

