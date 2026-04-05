import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem map_nsmul_eq_pow (ψ : AddChar A M) (n : ℕ) (x : A) : ψ (n • x) = ψ x ^ n := ψ.toMonoidHom.map_pow x n

