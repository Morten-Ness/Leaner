import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable {I : Type*} {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

variable (x : Π i, A i) (p : R[X])

theorem aeval_pi_apply : p.aeval x = fun j ↦ p.aeval (x j) := funext fun j ↦ Polynomial.aeval_pi_apply₂ x p j

