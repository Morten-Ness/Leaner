import Mathlib

variable {α : Type u}

variable {β : Type u}

theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeSemigroup β) = pure (f x) := rfl

