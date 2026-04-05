import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem swap_mul_of_ne {i j a : n} {b : m} (hai : a ≠ i) (haj : a ≠ j) (g : Matrix n m R) :
    (Matrix.swap R i j * g) a b = g a b := by
  simp [Matrix.swap, PEquiv.toMatrix_toPEquiv_mul, Equiv.swap_apply_of_ne_of_ne hai haj]

