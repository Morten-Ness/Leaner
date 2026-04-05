import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarRing A] [StarModule R A]
  [AddCommMonoid C] [Module R C] [StarAddMonoid C] [StarModule R C]

variable {n : Type*} [DecidableEq n] {B : n → Type*} [Π i, AddCommMonoid (B i)]
  [Π i, Module R (B i)] [Π i, StarAddMonoid (B i)] [∀ i, StarModule R (B i)]

variable [Fintype n]

theorem _root_.Pi.intrinsicStar_comul [Π i, CoalgebraStruct R (B i)]
    (h : ∀ i, star (toConv (comul (R := R) (A := B i))) =
      toConv (TensorProduct.comm R (B i) (B i) ∘ₗ comul)) :
    star (toConv (comul (R := R) (A := Π i, B i))) =
      toConv (TensorProduct.comm R (Π i, B i) (Π i, B i) ∘ₗ comul) := by
  ext i x
  have := by simpa using congr($(h i) x)
  simp only [coe_comp, coe_single, Function.comp_apply, intrinsicStar_apply, Pi.star_single,
    Pi.comul_single, LinearEquiv.coe_coe]
  rw [star_map_apply_eq_map_intrinsicStar, this, map_comm]
  simp

