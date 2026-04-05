import Mathlib

variable {α β : Type u}

theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeMagma β) = pure (f x) := rfl

