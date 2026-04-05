import Mathlib

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeMagma α → FreeMagma α → FreeMagma α) = fun x y ↦
      (· * ·) <$> traverse F x <*> traverse F y := rfl

