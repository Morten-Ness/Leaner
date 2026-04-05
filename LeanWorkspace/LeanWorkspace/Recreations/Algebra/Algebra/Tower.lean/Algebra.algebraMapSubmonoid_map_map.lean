import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

theorem Algebra.algebraMapSubmonoid_map_map {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (M : Submonoid R) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    algebraMapSubmonoid B (algebraMapSubmonoid A M) = algebraMapSubmonoid B M := algebraMapSubmonoid_map_eq _ (IsScalarTower.toAlgHom R A B)

