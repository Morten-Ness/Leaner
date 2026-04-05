import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

theorem _root_.TensorProduct.star_map_apply_eq_map_intrinsicStar
    (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] H)) (x) :
    star (TensorProduct.map f.ofConv g.ofConv x) =
      TensorProduct.map (star f).ofConv (star g).ofConv (star x) := by
  simpa using congr($(TensorProduct.intrinsicStar_map f g) (star x))

