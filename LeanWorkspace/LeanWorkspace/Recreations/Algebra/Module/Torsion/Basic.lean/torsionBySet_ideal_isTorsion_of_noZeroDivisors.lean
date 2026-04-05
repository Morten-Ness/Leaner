import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_ideal_isTorsion_of_noZeroDivisors [NoZeroDivisors R] [Nontrivial R]
    {I : Ideal R} (hbot : I ≠ ⊥) : IsTorsion R (Submodule.torsionBySet R M I) := by
  aesop (add norm Submodule.eq_bot_iff)

