import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem symm_symm (f : Equidecomp X G) : f.symm.symm = f := rfl

