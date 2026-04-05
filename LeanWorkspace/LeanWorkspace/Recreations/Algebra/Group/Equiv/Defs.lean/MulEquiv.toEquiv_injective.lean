import Mathlib

variable {F α β M N P G H : Type*}

theorem MulEquiv.toEquiv_injective {α β : Type*} [Mul α] [Mul β] :
    Function.Injective (toEquiv : (α ≃* β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
