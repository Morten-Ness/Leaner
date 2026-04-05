import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.toLin'_pow (M : Matrix n n R) (k : ℕ) :
    (M ^ k).toLin' = M.toLin' ^ k := by
  induction k with
  | zero => simp [End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin'_mul, ih, Module.End.mul_eq_comp]

