import Mathlib

open scoped AlgebraMonoidAlgebra

variable {R S T A B C M N O : Type*}

variable [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem isScalarTower_monoidAlgebra [CommSemiring T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] : IsScalarTower R S[M] T[M] := .of_algebraMap_eq' (MonoidAlgebra.mapAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.isScalarTower_monoidAlgebra
  AddMonoidAlgebra.vaddAssocClass_addMonoidAlgebra

