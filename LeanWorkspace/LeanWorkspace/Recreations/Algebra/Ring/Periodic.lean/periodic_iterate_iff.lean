import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem periodic_iterate_iff {f : α → α} {n : ℕ} {a : α} :
    Function.Periodic (f^[·] a) n ↔ IsPeriodicPt f n a := by
  refine ⟨fun h ↦ h.eq, fun h k ↦ ?_⟩
  simp only [Function.iterate_add_apply, h.eq]

alias ⟨Function.Periodic.isPeriodicPt, IsPeriodicPt.periodic_iterate⟩ := periodic_iterate_iff

