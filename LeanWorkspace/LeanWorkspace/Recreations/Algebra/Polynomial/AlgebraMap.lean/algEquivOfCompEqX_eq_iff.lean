import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem algEquivOfCompEqX_eq_iff (p q p' q' : R[X])
    (hpq : p.comp q = Polynomial.X) (hqp : q.comp p = Polynomial.X) (hpq' : p'.comp q' = Polynomial.X) (hqp' : q'.comp p' = Polynomial.X) :
    Polynomial.algEquivOfCompEqX p q hpq hqp = Polynomial.algEquivOfCompEqX p' q' hpq' hqp' ↔ p = p' := ⟨fun h ↦ by simpa using congr($h Polynomial.X), fun h ↦ by ext1; simp [h]⟩

