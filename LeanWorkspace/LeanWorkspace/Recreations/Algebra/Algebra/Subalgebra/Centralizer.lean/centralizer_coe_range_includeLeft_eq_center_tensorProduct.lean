import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_range_includeLeft_eq_center_tensorProduct [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_univ, ← Algebra.coe_top (R := R) (A := A),
    ← Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeLeft, includeLeftRingHom]

