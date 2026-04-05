import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

variable [DecompositionMonoid R]

theorem dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x := Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

