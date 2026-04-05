import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem toEquiv_trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := rfl

