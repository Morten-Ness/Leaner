import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem coe_aeval_mk_apply {S : Subalgebra R A} (h : x ∈ S) :
    (Polynomial.aeval (⟨x, h⟩ : S) p : A) = Polynomial.aeval x p := (Polynomial.aeval_algHom_apply S.val (⟨x, h⟩ : S) p).symm

