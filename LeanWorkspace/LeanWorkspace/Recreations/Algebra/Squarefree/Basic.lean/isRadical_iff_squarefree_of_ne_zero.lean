import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

variable [DecompositionMonoid R]

theorem isRadical_iff_squarefree_of_ne_zero (h : x ≠ 0) : IsRadical x ↔ Squarefree x := ⟨IsRadical.squarefree h, Squarefree.isRadical⟩

