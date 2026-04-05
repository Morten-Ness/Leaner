import Mathlib

open scoped Polynomial

theorem cardinalMk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : #(R[X]) = max #R ℵ₀ := (toFinsuppIso R).toEquiv.cardinal_eq.trans <| by
    rw [AddMonoidAlgebra, mk_finsupp_lift_of_infinite, lift_uzero, max_comm]
    rfl

