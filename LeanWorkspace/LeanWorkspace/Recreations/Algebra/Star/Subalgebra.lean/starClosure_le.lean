import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂.toSubalgebra) :
    S₁.starClosure ≤ S₂ := StarSubalgebra.toSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

