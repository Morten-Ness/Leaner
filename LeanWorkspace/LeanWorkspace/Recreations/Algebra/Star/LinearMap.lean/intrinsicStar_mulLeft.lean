import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

theorem intrinsicStar_mulLeft (x : E) :
    star (toConv (mulLeft R x)) = toConv (mulRight R (star x)) := by ext; simp

