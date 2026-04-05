import Mathlib

variable {α : Type u}

theorem map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R)
    [Invertible r] [ifr : Invertible (f r)] :
    f (⅟r) = ⅟(f r) := by
  obtain rfl : ifr = Invertible.map f r := Subsingleton.elim _ _; rfl

