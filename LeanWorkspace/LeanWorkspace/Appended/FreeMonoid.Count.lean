import Mathlib

section

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP'_mul (l₁ l₂ : FreeMonoid α) : (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p := by
  dsimp [FreeMonoid.countP']
  simp only [List.countP_append]

end
