import Mathlib

variable {α : Type u}

variable {β : Type v} [Semigroup β] (f : α → β)

theorem lift_of_mul (x y) : FreeSemigroup.lift f (FreeSemigroup.of x * y) = f x * FreeSemigroup.lift f y := by rw [map_mul, FreeSemigroup.lift_of]

