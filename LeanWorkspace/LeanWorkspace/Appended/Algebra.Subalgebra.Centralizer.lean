import Mathlib

section

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_map_includeLeft_eq_center_tensorProduct
    (S : Subalgebra R A) [Module.Free R B] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeLeft (R := R) (B := B))) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer R (S : Set A)).val
      (AlgHom.id R B)).range :=
  Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct R A B S

end

section

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

end

section

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_tensorProduct_eq_center_tensorProduct_left [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

end
