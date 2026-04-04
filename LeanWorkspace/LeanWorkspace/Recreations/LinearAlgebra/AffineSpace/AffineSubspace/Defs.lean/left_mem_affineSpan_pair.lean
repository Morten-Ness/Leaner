import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ ∈ line[k, p₁, p₂] := mem_affineSpan _ (Set.mem_insert _ _)

