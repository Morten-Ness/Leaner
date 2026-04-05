import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq (f : A →ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range := SetLike.coe_injective Set.image_preimage_eq_inter_range

