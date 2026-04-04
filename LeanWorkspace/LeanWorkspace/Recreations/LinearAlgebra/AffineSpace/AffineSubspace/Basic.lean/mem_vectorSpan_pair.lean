import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem mem_vectorSpan_pair {p₁ p₂ : P} {v : V} :
    v ∈ vectorSpan k ({p₁, p₂} : Set P) ↔ ∃ r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vectorSpan_pair, Submodule.mem_span_singleton]

