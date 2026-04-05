import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_univ, ← Algebra.coe_top (R := R) (A := B),
    ← Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeRight]

