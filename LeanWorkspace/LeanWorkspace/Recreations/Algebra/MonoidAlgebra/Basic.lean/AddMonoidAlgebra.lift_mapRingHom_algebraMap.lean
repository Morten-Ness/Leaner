import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

set_option backward.isDefEq.respectTransparency false in
theorem lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A]
    [Algebra R S] [IsScalarTower R S A]
    (f : Multiplicative M →* A) (x : R[M]) :
    AddMonoidAlgebra.lift _ _ _ f (mapRingHom _ (algebraMap R S) x) = AddMonoidAlgebra.lift _ _ _ f x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

