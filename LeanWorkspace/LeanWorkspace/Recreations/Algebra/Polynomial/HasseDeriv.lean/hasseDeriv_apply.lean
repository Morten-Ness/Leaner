import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_apply :
    Polynomial.hasseDeriv k f = f.sum fun i r => monomial (i - k) (↑(i.choose k) * r) := by
  dsimp [Polynomial.hasseDeriv]
  simp

