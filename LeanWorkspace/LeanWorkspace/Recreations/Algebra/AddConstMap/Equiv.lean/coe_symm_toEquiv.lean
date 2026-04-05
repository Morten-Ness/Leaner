import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem coe_symm_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv.symm = e.symm := rfl

