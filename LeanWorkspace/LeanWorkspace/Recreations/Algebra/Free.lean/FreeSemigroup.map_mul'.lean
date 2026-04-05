import Mathlib

variable {α : Type u}

variable {β : Type u}

theorem map_mul' (f : α → β) (x y : FreeSemigroup α) : f <$> (x * y) = f <$> x * f <$> y := map_mul (FreeSemigroup.map f) _ _

