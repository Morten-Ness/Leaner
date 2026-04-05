import Mathlib

variable {ι α β M N P G : Type*}

theorem length_sigma {σ : α → Type*} (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map fun a ↦ length (l₂ a)).sum := by
  induction l₁ with
  | nil => rfl
  | cons x l₁ IH => simp only [sigma_cons, length_append, length_map, IH, map, sum_cons]

