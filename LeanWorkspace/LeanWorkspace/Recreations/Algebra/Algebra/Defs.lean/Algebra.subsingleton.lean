import Mathlib

theorem Algebra.subsingleton (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
    [Subsingleton R] : Subsingleton A := (algebraMap R A).codomain_trivial

