import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (NonUnitalSubalgebra.map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) := by
  intro S T h
  ext x
  constructor
  · intro hx
    have hmem : f x ∈ (NonUnitalSubalgebra.map f S : NonUnitalSubalgebra R B) := ⟨x, hx, rfl⟩
    rw [h] at hmem
    rcases hmem with ⟨y, hy, hyx⟩
    exact hf (hyx.trans rfl.symm) ▸ hy
  · intro hx
    have hmem : f x ∈ (NonUnitalSubalgebra.map f T : NonUnitalSubalgebra R B) := ⟨x, hx, rfl⟩
    rw [← h] at hmem
    rcases hmem with ⟨y, hy, hyx⟩
    exact hf (hyx.trans rfl.symm) ▸ hy
