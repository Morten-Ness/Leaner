import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem addHom_ext' {M : Type*} [AddZeroClass M] {f g : R[X] →+ M}
    (h : ∀ n, f.comp (Polynomial.monomial n).toAddMonoidHom = g.comp (Polynomial.monomial n).toAddMonoidHom) : f = g := Polynomial.addHom_ext fun n => DFunLike.congr_fun (h n)

