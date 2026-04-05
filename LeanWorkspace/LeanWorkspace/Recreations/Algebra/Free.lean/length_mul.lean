import Mathlib

variable {α : Type u}

theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  simp [FreeSemigroup.length, Nat.add_right_comm, List.length, List.length_append]

