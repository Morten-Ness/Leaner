import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem _root_.List.periodic_prod [Add α] [MulOneClass β] (l : List (α → β))
    (hl : ∀ f ∈ l, Function.Periodic f c) : Function.Periodic l.prod c := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)

