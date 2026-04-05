import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.comp_addHom [Add α] [Add γ] (h : Function.Periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : Function.Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]

