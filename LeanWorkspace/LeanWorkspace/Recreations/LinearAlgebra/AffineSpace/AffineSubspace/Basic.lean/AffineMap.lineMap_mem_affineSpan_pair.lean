import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem AffineMap.lineMap_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₁ p₂ r ∈ line[k, p₁, p₂] := AffineMap.lineMap_mem _ (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

