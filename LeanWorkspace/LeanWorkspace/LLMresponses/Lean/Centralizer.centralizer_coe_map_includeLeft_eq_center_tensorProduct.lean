FAIL
import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_map_includeLeft_eq_center_tensorProduct
    (S : Subalgebra R A) [Module.Free R B] :
    Subalgebra.centralizer R
      ((S.map (Algebra.TensorProduct.includeLeft (R := R) (A := A) (B := B)) :
        Subalgebra R (TensorProduct R A B)) : Set (TensorProduct R A B)) =
        (((Subalgebra.center R S).map
          ((Algebra.TensorProduct.includeLeft (R := R) (A := S) (B := B)).comp
            (S.val : S →ₐ[R] A))) : Subalgebra R (TensorProduct R A B)) := by
  simpa using
    Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct
      (R := R) (A := A) (B := B) S
