import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [CommSemiring R]

set_option linter.docPrime false in
theorem trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    Matrix.trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = Matrix.trace N := Matrix.trace_units_conj M⁻¹ N

