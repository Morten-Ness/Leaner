import Mathlib

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

theorem traverse_pure (x) : traverse F (pure x : FreeSemigroup α) = pure <$> F x := rfl

