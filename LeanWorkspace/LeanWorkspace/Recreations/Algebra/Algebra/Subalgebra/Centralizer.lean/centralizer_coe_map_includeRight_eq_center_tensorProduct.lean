import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_map_includeRight_eq_center_tensorProduct
    (S : Subalgebra R B) [Module.Free R A] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range :=
  Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct R A B S

