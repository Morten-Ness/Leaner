import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem «exists» : ∃ p, CharP R p := by
  classical
  exact ⟨ringChar R, inferInstance⟩
