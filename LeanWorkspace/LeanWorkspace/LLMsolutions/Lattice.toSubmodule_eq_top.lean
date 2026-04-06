import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ := by
  constructor
  · intro h
    ext x
    change x ∈ S.toSubmodule ↔ x ∈ (⊤ : Subalgebra R A)
    rw [h]
    simp
  · intro h
    rw [h]
    ext x
    simp
