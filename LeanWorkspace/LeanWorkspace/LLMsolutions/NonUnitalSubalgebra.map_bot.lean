FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem map_bot [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A →ₙₐ[R] B) : (⊥ : NonUnitalSubalgebra R A).map f = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [NonUnitalSubalgebra.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [show y = 0 by simpa using hy]
    simp
  · intro hx
    rw [NonUnitalSubalgebra.mem_map]
    refine ⟨0, ?_, ?_⟩
    · simpa using hx
    · rw [show x = 0 by simpa using hx]
      simp
