import Mathlib

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

theorem pow_apply (f : G →+c[a, a] G) (n : ℕ) (x : G) : (f ^ n) x = f^[n] x := rfl

