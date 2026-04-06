import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem toNonUnitalSubalgebra_le_toNonUnitalSubalgebra {S T : Subalgebra R A} :
    S.toNonUnitalSubalgebra ≤ T.toNonUnitalSubalgebra ↔ S ≤ T := by
  rfl
