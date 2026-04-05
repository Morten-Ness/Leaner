import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R B]

theorem injective_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (StarAlgHom.codRestrict f S hf) ↔ Function.Injective f := ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

