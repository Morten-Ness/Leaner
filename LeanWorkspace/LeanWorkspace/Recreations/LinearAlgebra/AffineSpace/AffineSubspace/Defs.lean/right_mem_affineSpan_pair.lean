import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ ∈ line[k, p₁, p₂] := mem_affineSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

