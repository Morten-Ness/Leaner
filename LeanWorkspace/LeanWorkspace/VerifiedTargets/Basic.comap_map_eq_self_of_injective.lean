import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem comap_map_eq_self_of_injective
    {f : A →ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S := SetLike.coe_injective (Set.preimage_image_eq _ hf)

