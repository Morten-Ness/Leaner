import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem range_zmultiplesHom (a : A) : (zmultiplesHom A a).range = zmultiples a := rfl

