import Mathlib

variable {α : Type u}

variable {β : Type u}

theorem mul_seq {f g : FreeSemigroup (α → β)} {x : FreeSemigroup α} :
    f * g <*> x = (f <*> x) * (g <*> x) := FreeSemigroup.mul_bind _ _ _

