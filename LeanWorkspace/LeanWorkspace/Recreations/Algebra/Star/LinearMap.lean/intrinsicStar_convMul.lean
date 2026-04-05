import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarRing A] [StarModule R A]
  [AddCommMonoid C] [Module R C] [StarAddMonoid C] [StarModule R C]

theorem intrinsicStar_convMul [CoalgebraStruct R C]
    (h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul))
    (f g : WithConv (C →ₗ[R] A)) : star (f * g) = star g * star f := by
  simp_rw [convMul_def, LinearMap.intrinsicStar_comp', LinearMap.intrinsicStar_mul', intrinsicStar_map,
    h, comp_assoc, ← comp_assoc _ _ (map _ _), map_comp_comm_eq,
    ← comp_assoc _ (TensorProduct.comm R A A).toLinearMap]
  ext; simp

