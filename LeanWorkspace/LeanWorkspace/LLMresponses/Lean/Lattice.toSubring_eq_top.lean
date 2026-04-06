import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ := by
  constructor
  · intro h
    ext x
    change x ∈ S.toSubring ↔ x ∈ (⊤ : Subalgebra R A)
    rw [h]
    simp
  · intro h
    rw [h]
    rfl
