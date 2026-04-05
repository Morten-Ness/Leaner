import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem algHom_ext' {f g : A[X] →ₐ[R] B}
    (hC : f.comp Polynomial.CAlgHom = g.comp Polynomial.CAlgHom)
    (hX : f Polynomial.X = g Polynomial.X) : f = g := AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

