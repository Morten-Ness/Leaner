import Mathlib

variable {R A B C : Type*} [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]

variable [StarModule R B] [StarModule R C]

theorem starMap_injective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (Unitization.starMap φ) := by
  intro x y h
  ext
  · simpa using congr($(h).fst)
  · exact hφ <| by simpa [Unitization.algebraMap_eq_inl] using congr($(h).snd)

