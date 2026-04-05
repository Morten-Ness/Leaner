import Mathlib

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

theorem traverse_mul (x y : FreeMagma α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y := rfl

