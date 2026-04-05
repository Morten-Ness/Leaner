import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg]
  rfl

