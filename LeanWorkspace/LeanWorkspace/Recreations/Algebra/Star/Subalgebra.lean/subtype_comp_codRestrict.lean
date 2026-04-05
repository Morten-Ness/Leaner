import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R B]

theorem subtype_comp_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B)
    (hf : ∀ x : A, f x ∈ S) : S.subtype.comp (f.codRestrict S hf) = f := StarAlgHom.ext <| StarAlgHom.coe_codRestrict _ S hf

