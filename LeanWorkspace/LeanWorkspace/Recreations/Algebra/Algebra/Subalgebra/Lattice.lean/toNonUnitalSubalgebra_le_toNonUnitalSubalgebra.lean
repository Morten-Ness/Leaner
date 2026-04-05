import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem toNonUnitalSubalgebra_le_toNonUnitalSubalgebra {S T : Subalgebra R A} :
    S.toNonUnitalSubalgebra ≤ T.toNonUnitalSubalgebra ↔ S ≤ T := Subalgebra.toNonUnitalSubalgebraOrderEmbedding.le_iff_le

alias ⟨_, toNonUnitalSubalgebra_mono⟩ := toNonUnitalSubalgebra_le_toNonUnitalSubalgebra

