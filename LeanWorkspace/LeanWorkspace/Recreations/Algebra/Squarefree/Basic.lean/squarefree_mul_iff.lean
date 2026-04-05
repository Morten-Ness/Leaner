import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

variable [DecompositionMonoid R]

theorem squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y := ⟨fun h ↦ ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd ↦ hp (Squarefree.dvd_of_squarefree_of_mul_dvd_mul_left sqy dvd)
      (Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right sqx dvd)⟩

