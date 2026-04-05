import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem symm_bijective : Function.Bijective (Equidecomp.symm : Equidecomp X G → _) := Equidecomp.symm_involutive.bijective

