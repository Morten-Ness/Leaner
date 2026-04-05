import Mathlib

variable (R : Type u) [Semiring R]

theorem forget_map {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    (forget (SemimoduleCat.{v} R)).map f = (f : _ → _) := rfl

