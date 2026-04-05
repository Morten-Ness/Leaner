import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem Nontrivial.of_polynomial_ne (h : p ≠ q) : Nontrivial R := (subsingleton_or_nontrivial R).resolve_left fun _hI => h <| Subsingleton.elim _ _

