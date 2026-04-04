import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_pair_le_of_left_mem {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    line[k, p₁, p₃] ≤ line[k, p₂, p₃] := affineSpan_pair_le_of_mem_of_mem h (right_mem_affineSpan_pair _ _ _)

