import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

variable [DecompositionMonoid R]

theorem isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0 := ⟨fun hx ↦ (em <| x = 0).elim .inr fun h ↦ .inl <| hx.squarefree h,
    Or.rec Squarefree.isRadical <| by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

