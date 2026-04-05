import Mathlib

variable {α : Type u} {β : Type v}

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

theorem withBotCongr_refl : (AddEquiv.refl α).withBotCongr = AddEquiv.refl _ := AddEquiv.ext <| congr_fun WithBot.map_id

