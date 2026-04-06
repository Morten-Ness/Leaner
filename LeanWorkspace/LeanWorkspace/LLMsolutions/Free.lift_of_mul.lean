FAIL
import Mathlib

variable {α : Type u}

variable {β : Type v} [Semigroup β] (f : α → β)

theorem lift_of_mul (x y) : FreeSemigroup.lift f (FreeSemigroup.of x * y) = f x * FreeSemigroup.lift f y := by
  cases y with
  | mk head tail =>
      simp [FreeSemigroup.of, FreeSemigroup.lift]
      induction tail generalizing head with
      | nil =>
          simp
      | cons a t ih =>
          simp [List.foldl_cons, mul_assoc, ih]
