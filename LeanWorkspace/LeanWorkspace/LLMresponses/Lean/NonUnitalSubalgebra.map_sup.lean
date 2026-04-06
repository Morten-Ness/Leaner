FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem map_sup [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (S T : NonUnitalSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalSubalgebra R B) = S.map f ⊔ T.map f := by
  rw [eq_iff_le_not_lt]
  constructor
  · intro h
    exact le_sup_of_le_left <| map_mono f <| le_sup_left
  · intro h
    exact le_sup_of_le_right <| map_mono f <| le_sup_right
  · intro h
    have hST : S.map f ⊔ T.map f ≤ (S ⊔ T).map f := by
      exact sup_le (map_mono f le_sup_left) (map_mono f le_sup_right)
    exact h (le_antisymm hST (sup_le (map_mono f le_sup_left) (map_mono f le_sup_right)))
