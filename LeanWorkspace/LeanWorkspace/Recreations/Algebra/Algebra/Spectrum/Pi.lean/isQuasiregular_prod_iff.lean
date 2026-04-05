import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B) :
    IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular b := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!

