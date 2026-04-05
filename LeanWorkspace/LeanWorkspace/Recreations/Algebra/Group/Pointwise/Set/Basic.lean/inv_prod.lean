import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem inv_prod [Inv β] (s : Set α) (t : Set β) : (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := rfl

