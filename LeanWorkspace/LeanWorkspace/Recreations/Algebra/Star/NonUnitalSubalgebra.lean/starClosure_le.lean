import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [StarModule R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
    (h : S₁ ≤ S₂.toNonUnitalSubalgebra) : S₁.starClosure ≤ S₂ := NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

