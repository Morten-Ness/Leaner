import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  constructor
  · intro hs
    rw [Finset.isUnit_iff] at hs
    simpa [SetLike.exists] using hs
  · rintro ⟨a, rfl⟩
    exact Finset.isUnit_singleton a
