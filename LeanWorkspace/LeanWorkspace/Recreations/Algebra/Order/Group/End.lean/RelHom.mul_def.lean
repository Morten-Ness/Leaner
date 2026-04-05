import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem mul_def (f g : r →r r) : (f * g) = f.comp g := rfl

