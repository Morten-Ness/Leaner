import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →⋆ₐ[R] B) (hf : Function.Injective f)
    (s : ι → StarSubalgebra R A) : StarSubalgebra.map f (iInf s) = ⨅ (i : ι), StarSubalgebra.map f (s i) := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

