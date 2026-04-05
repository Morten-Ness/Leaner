import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_pow (a) (n : ℕ) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero        => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

