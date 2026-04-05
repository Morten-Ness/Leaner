import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι := finite_of_fin_dim_affineIndependent k b.ind

