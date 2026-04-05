import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S := ⟨fun h x => by rw [h]; exact NonUnitalStarAlgebra.mem_top,
    fun h => by NonUnitalStarSubalgebra.ext x; exact ⟨fun _ => NonUnitalStarAlgebra.mem_top, fun _ => h x⟩⟩

