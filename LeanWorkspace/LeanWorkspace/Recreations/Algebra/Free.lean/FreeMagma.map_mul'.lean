import Mathlib

variable {α β : Type u}

theorem map_mul' (f : α → β) (x y : FreeMagma α) : f <$> (x * y) = f <$> x * f <$> y := rfl

