FAIL
import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι → Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    exact Subsemiring.map_mono ((le_iSup S i))
  · refine iSup_le ?_
    intro i
    exact (Subalgebra.toSubsemiring_mono (le_iSup S i))
