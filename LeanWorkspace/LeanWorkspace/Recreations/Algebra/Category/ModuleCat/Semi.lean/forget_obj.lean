import Mathlib

variable (R : Type u) [Semiring R]

theorem forget_obj {M : SemimoduleCat.{v} R} : (forget (SemimoduleCat.{v} R)).obj M = M := rfl

