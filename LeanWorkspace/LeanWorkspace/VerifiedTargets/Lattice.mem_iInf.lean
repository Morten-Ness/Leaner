import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Algebra.mem_sInf, Set.forall_mem_range]

