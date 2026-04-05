import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem mapRingHom_comp_C {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    (Polynomial.mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := by ext; simp

