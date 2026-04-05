import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem comap_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f) :
    Function.Injective (StarSubalgebra.comap f) := fun _S₁ _S₂ h =>
  StarSubalgebra.ext fun b =>
    let ⟨x, hx⟩ := hf b
    let this := SetLike.ext_iff.1 h x
    hx ▸ this

