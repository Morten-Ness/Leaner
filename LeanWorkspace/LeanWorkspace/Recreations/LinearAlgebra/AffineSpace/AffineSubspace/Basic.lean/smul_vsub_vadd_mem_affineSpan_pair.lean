import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem smul_vsub_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) +ᵥ p₁ ∈ line[k, p₁, p₂] := AffineMap.lineMap_mem_affineSpan_pair _ _ _

