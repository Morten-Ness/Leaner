import Mathlib

variable {R : Type*} [Mul R]

theorem isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c := ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

