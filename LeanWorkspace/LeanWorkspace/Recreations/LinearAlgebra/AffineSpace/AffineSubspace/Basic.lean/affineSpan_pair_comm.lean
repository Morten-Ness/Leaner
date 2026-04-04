import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem affineSpan_pair_comm {p₁ p₂ : P} :
    line[k, p₁, p₂] = line[k, p₂, p₁] := by
  rw [Set.pair_comm]

