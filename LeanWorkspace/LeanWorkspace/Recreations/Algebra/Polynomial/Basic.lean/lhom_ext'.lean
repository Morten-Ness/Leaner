import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem lhom_ext' {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] →ₗ[R] M}
    (h : ∀ n, f.comp (Polynomial.monomial n) = g.comp (Polynomial.monomial n)) : f = g := LinearMap.toAddMonoidHom_injective <| Polynomial.addHom_ext fun n => LinearMap.congr_fun (h n)

-- this has the same content as the subsingleton

