import Mathlib

variable {α : Type u}

variable {β : Type u}

theorem pure_seq {f : α → β} {x : FreeSemigroup α} : pure f <*> x = f <$> x := rfl

