import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι → Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  simp only [iSup, Set.range_nonempty, Algebra.sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

