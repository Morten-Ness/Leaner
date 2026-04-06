FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_union (s t : Set A) : NonUnitalAlgebra.adjoin R (s ∪ t) = NonUnitalAlgebra.adjoin R s ⊔ NonUnitalAlgebra.adjoin R t := by
  refine le_antisymm ?_ ?_
  · refine NonUnitalAlgebra.adjoin_le ?_
    intro x hx
    rcases hx with hx | hx
    · exact show x ∈ NonUnitalAlgebra.adjoin R s ⊔ NonUnitalAlgebra.adjoin R t from
        show x ∈ NonUnitalAlgebra.adjoin R s from
          NonUnitalAlgebra.subset_adjoin R hx
    · exact show x ∈ NonUnitalAlgebra.adjoin R s ⊔ NonUnitalAlgebra.adjoin R t from
        show x ∈ NonUnitalAlgebra.adjoin R t from
          NonUnitalAlgebra.subset_adjoin R hx
  · refine sup_le ?_ ?_
    · exact NonUnitalAlgebra.adjoin_le fun x hx =>
        NonUnitalAlgebra.subset_adjoin R (Or.inl hx)
    · exact NonUnitalAlgebra.adjoin_le fun x hx =>
        NonUnitalAlgebra.subset_adjoin R (Or.inr hx)
