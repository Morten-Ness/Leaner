import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem toEquiv_symm (e : G ≃+c[a, b] H) : e.symm.toEquiv = e.toEquiv.symm := rfl

