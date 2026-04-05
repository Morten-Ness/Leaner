import Mathlib

variable {α β : Type u}

theorem pure_seq {α β : Type u} {f : α → β} {x : FreeMagma α} : pure f <*> x = f <$> x := rfl

