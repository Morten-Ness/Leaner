import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem IsUnit.exists_right_inv (h : IsUnit a) : ∃ b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩

