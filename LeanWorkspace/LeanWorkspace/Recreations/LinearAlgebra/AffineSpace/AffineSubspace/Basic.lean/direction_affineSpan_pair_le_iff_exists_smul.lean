import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem direction_affineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁].direction ≤ line[k, p₂, q₂].direction ↔ ∃ z : k, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair_rev, vectorSpan_pair_rev,
    Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]

