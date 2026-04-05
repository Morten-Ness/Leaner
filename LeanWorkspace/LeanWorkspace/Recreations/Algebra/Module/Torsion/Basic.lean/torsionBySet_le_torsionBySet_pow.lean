import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_le_torsionBySet_pow (i j : ℕ) (h : i ≤ j) (I : Ideal R) :
    Submodule.torsionBySet R M ↑(I ^ i) ≤ Submodule.torsionBySet R M ↑(I ^ j) := Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_pow_right h)

