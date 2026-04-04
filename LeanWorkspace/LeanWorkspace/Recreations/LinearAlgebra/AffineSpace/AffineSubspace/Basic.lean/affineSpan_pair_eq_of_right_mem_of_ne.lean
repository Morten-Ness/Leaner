import Mathlib

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem affineSpan_pair_eq_of_right_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃])
    (hne : p₁ ≠ p₂) :
    line[k, p₂, p₁] = line[k, p₂, p₃] := affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) h hne.symm

