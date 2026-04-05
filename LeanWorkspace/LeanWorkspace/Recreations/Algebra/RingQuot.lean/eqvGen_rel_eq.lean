import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

theorem eqvGen_rel_eq (r : R → R → Prop) : Relation.EqvGen (Rel r) = RingConGen.Rel r := by
  ext x₁ x₂
  constructor
  · intro h
    induction h with
    | rel _ _ h => induction h with
      | of => exact RingConGen.Rel.of _ _ ‹_›
      | add_left _ h => exact h.add (RingConGen.Rel.refl _)
      | mul_left _ h => exact h.mul (RingConGen.Rel.refl _)
      | mul_right _ h => exact (RingConGen.Rel.refl _).mul h
    | refl => exact RingConGen.Rel.refl _
    | symm => exact RingConGen.Rel.symm ‹_›
    | trans => exact RingConGen.Rel.trans ‹_› ‹_›
  · intro h
    induction h with
    | of => exact Relation.EqvGen.rel _ _ (Rel.of ‹_›)
    | refl => exact (RingQuot.ringCon r).refl _
    | symm => exact (RingQuot.ringCon r).symm ‹_›
    | trans => exact (RingQuot.ringCon r).trans ‹_› ‹_›
    | add => exact (RingQuot.ringCon r).add ‹_› ‹_›
    | mul => exact (RingQuot.ringCon r).mul ‹_› ‹_›

