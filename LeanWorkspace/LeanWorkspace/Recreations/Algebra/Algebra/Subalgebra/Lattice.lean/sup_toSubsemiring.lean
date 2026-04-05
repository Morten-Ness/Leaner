import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem sup_toSubsemiring (S T : Subalgebra R A) :
    (S ⊔ T).toSubsemiring = S.toSubsemiring ⊔ T.toSubsemiring := by
  rw [← S.toSubsemiring.closure_eq, ← T.toSubsemiring.closure_eq, ← Subsemiring.closure_union]
  simp_rw [Algebra.sup_def, adjoin_toSubsemiring, Subalgebra.coe_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

