import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem semiconj [Add G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    Semiconj f (· + a) (· + b) := map_add_const f

