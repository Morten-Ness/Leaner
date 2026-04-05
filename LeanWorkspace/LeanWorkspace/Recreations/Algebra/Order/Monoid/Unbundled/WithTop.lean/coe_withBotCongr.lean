import Mathlib

variable {α : Type u} {β : Type v}

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

theorem coe_withBotCongr : e.withBotCongr = WithBot.map e := rfl

