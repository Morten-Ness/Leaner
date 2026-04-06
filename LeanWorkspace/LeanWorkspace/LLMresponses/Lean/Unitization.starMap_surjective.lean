FAIL
import Mathlib

variable {R A B C : Type*} [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]

variable [StarModule R B] [StarModule R C]

theorem starMap_surjective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Surjective φ) :
    Function.Surjective (Unitization.starMap φ) := by
  intro x
  rcases x with ⟨r, b⟩
  rcases hφ b with ⟨a, rfl⟩
  refine ⟨Unitization.inr r + Unitization.of a, ?_⟩
  simp [Unitization.starMap_inr, Unitization.starMap_of]
