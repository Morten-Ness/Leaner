import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : R[X] →+ M}
    (h : ∀ n a, f (Polynomial.monomial n a) = g (Polynomial.monomial n a)) : f = g := AddMonoidHom.eq_of_eqOn_denseM Polynomial.addSubmonoid_closure_setOf_eq_monomial <| by
    rintro p ⟨n, a, rfl⟩
    exact h n a

