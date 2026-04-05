import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem symm_involutive : Function.Involutive (Equidecomp.symm : Equidecomp X G → _) := Equidecomp.symm_symm

