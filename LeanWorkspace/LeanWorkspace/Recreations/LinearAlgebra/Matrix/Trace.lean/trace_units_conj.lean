import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [CommSemiring R]

theorem trace_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    Matrix.trace ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = Matrix.trace N := by
  rw [Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

