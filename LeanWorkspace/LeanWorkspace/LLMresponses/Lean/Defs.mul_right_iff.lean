FAIL
import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_right_iff {a b : M} (hb : IsUnit b) :
    IsUnit (a * b) ↔ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    rcases hb with ⟨v, rfl⟩
    refine ⟨u * v⁻¹, ?_⟩
    simp [Units.val_mul, mul_assoc]
  · intro ha
    exact ha.mul hb
