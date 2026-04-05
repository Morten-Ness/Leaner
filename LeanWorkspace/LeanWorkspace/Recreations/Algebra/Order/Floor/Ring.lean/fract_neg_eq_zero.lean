import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_neg_eq_zero {x : R} : fract (-x) = 0 ↔ fract x = 0 := by
  simp only [Int.fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

