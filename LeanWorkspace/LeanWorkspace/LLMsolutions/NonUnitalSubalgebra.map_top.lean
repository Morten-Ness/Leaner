import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem map_top (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp, rfl⟩
