import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_bot : (⊥ : Submodule R M).spanFinrank = 0 := by simp [Submodule.spanFinrank]

