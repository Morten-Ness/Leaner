import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable [Mul N]

theorem eq_of_eqOn_dense {s : Set M} (hs : Subsemigroup.closure s = ⊤) {f g : M →ₙ* N} (h : s.EqOn f g) :
    f = g := eq_of_eqOn_top <| hs ▸ MulHom.eqOn_closure h

