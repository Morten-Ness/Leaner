import Mathlib

variable {α : Type u} {β : Type v}

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

theorem withBotCongr_trans :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr := by
  ext x
  simp

