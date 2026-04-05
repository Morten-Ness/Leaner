import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

