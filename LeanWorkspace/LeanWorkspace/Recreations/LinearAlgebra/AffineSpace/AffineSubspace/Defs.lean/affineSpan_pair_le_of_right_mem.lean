import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_pair_le_of_right_mem {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    line[k, p₂, p₁] ≤ line[k, p₂, p₃] := affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) h

