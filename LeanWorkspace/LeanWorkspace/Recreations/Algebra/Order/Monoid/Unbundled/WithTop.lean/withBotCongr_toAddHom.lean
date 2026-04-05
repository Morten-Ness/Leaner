import Mathlib

variable {α : Type u} {β : Type v}

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

theorem withBotCongr_toAddHom : e.withBotCongr = (e : AddHom α β).withBotMap := rfl

