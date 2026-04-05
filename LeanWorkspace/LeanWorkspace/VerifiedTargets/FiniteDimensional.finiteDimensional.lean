import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finiteDimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V := let ⟨i⟩ := b.nonempty
  (b.basisOf i).finiteDimensional_of_finite

