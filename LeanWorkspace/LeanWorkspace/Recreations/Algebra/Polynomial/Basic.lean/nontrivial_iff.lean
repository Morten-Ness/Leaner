import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

theorem nontrivial_iff [Semiring R] : Nontrivial R[X] ↔ Nontrivial R := ⟨fun h =>
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Polynomial.Nontrivial.of_polynomial_ne hrs,
    fun h => @Polynomial.nontrivial _ _ h⟩

