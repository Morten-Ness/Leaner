import Mathlib

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

theorem mul_def (f g : G →+c[a, a] G) : f * g = f.comp g := rfl

