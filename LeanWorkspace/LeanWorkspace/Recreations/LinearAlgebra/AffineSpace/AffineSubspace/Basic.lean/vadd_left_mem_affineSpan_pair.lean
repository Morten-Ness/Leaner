import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem vadd_left_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₁ ∈ line[k, p₁, p₂] ↔ ∃ r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _), direction_affineSpan,
    mem_vectorSpan_pair_rev]

