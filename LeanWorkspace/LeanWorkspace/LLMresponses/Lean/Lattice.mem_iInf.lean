import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp [show x ∈ (iInf S : Subalgebra R A) ↔ x ∈ ↑(iInf S : Subalgebra R A) by rfl]
