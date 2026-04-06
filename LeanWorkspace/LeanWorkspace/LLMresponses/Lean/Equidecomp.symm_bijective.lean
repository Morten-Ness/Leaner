import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem symm_bijective : Function.Bijective (Equidecomp.symm : Equidecomp X G → _) :=
by
  constructor
  · intro a b h
    simpa using congrArg Equidecomp.symm h
  · intro a
    refine ⟨Equidecomp.symm a, ?_⟩
    simp
