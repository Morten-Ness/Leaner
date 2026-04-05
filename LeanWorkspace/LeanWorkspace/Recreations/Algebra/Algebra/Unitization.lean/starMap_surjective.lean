import Mathlib

variable {R A B C : Type*} [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]

variable [StarModule R B] [StarModule R C]

theorem starMap_surjective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Surjective φ) :
    Function.Surjective (Unitization.starMap φ) := by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨Unitization.mk (r, a), by rfl⟩

