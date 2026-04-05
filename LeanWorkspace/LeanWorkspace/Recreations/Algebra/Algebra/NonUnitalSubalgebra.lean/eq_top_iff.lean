import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem eq_top_iff {S : NonUnitalSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S := ⟨fun h x => by rw [h]; exact NonUnitalAlgebra.mem_top, fun h => by NonUnitalSubalgebra.ext x; exact ⟨fun _ => NonUnitalAlgebra.mem_top, fun _ => h x⟩⟩

