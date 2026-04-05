import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_fn_apply {Polynomial.X : Type*} (g : R[X]) (f : Polynomial.X → R) (x : Polynomial.X) :
    ((Polynomial.aeval f) g) x = Polynomial.aeval (f x) g := (Polynomial.aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm

