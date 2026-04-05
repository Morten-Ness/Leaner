import Mathlib

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

theorem traverse_pure' : traverse F ∘ pure = fun x ↦ (pure <$> F x : m (FreeSemigroup β)) := rfl

