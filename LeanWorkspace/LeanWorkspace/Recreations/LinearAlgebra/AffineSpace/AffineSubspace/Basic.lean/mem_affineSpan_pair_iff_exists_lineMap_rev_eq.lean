import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem mem_affineSpan_pair_iff_exists_lineMap_rev_eq {p p₁ p₂ : P} :
    p ∈ line[k, p₁, p₂] ↔ ∃ r : k, AffineMap.lineMap p₂ p₁ r = p := by
  rw [Set.pair_comm, mem_affineSpan_pair_iff_exists_lineMap_eq]

