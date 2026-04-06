FAIL
import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι := by
  classical
  by_cases h : Nonempty ι
  · let i : ι := Classical.choice h
    let e := (b.basisOf i).repr.symm
    haveI : Finite (ι \ {i}) := Finite.of_equiv _ e
    exact finite_coe_iff.mp inferInstance
  · have : IsEmpty ι := not_nonempty_iff.mp h
    exact Finite.of_isEmpty ι
