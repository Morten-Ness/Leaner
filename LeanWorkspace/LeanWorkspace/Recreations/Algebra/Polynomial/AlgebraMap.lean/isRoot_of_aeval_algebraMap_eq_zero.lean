import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable [Semiring S] {f : R →+* S}

theorem isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] [FaithfulSMul R S] {p : R[X]} {r : R}
    (hr : p.aeval (algebraMap R S r) = 0) : p.IsRoot r := Polynomial.isRoot_of_eval₂_map_eq_zero (FaithfulSMul.algebraMap_injective _ _) hr

