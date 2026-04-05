import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.of_isScalarTower {f : R[X]} {A : Type*} (B : Type*) [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hf : Polynomial.Splits (f.map (algebraMap R A))) : Polynomial.Splits (f.map (algebraMap R B)) := hf.of_algHom (IsScalarTower.toAlgHom R A B)

