import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_tensorProduct_eq_center_tensorProduct_right [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (Algebra.ofId R A) (AlgHom.id R B)).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

