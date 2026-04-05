import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

set_option backward.isDefEq.respectTransparency false in
theorem lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A]
    [Algebra R S] [IsScalarTower R S A]
    (f : M →* A) (x : R[M]) :
    MonoidAlgebra.lift _ _ _ f (mapRingHom _ (algebraMap R S) x) = MonoidAlgebra.lift _ _ _ f x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

