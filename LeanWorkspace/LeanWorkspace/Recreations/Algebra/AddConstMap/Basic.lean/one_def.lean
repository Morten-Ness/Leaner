import Mathlib

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

theorem one_def : (1 : G →+c[a, a] G) = .id := rfl

