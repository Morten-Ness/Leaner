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

theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr :
    starLinearEquiv R (A := WithConv (E →ₗ[R] F)) =
      (WithConv.linearEquiv R _).trans
      (((starLinearEquiv R).arrowCongr (starLinearEquiv R)).trans
        (WithConv.linearEquiv R _).symm) := rfl

