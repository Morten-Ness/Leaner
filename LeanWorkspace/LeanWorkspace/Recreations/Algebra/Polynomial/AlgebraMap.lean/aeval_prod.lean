import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_prod (x : A × B) : Polynomial.aeval (R := R) x = (Polynomial.aeval x.1).prod (Polynomial.aeval x.2) :=
  Polynomial.aeval_algHom (.fst R A B) x ▸ Polynomial.aeval_algHom (.snd R A B) x ▸
    (Polynomial.aeval x).prod_comp (.fst R A B) (.snd R A B)

