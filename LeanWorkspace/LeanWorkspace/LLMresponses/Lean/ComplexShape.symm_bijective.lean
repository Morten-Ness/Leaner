import Mathlib

variable {ι : Type*}

theorem symm_bijective :
    Function.Bijective (ComplexShape.symm : ComplexShape ι → ComplexShape ι) :=
by
  refine ⟨?_, ?_⟩
  · intro a b h
    simpa using congrArg ComplexShape.symm h
  · intro a
    refine ⟨ComplexShape.symm a, ?_⟩
    simp
