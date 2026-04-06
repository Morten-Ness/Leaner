FAIL
import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem le_one_iff {p : Associates M} : p ≤ 1 ↔ p = 1 := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    have ha' : p * a = 1 := ha.symm
    have hunit : IsUnit (p * a) := by simpa [ha'] using (isUnit_one : IsUnit (1 : Associates M))
    rcases hunit.mul.mp hunit with ⟨hp, hau⟩
    exact Associates.eq_one_iff_isUnit.mpr hp
  · intro h
    rw [h]
