FAIL
import Mathlib

variable {α : Type u}

theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  cases x with
  | mk hx tx =>
      cases y with
      | mk hy ty =>
          simp [FreeSemigroup.length, HAppend.hAppend, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
