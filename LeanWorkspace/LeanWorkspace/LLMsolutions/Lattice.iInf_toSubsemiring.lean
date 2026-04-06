import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iInf_toSubsemiring {ι : Sort*} (S : ι → Subalgebra R A) :
    (iInf S).toSubsemiring = ⨅ i, (S i).toSubsemiring := by
  ext x
  change x ∈ iInf S ↔ x ∈ ⨅ i, (S i).toSubsemiring
  simp [iInf, sInf_image]
