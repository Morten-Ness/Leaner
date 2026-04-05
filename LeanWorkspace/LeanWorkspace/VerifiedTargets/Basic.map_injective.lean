import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (Subalgebra.map f) := fun _S₁ _S₂ ih =>
  Subalgebra.ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

