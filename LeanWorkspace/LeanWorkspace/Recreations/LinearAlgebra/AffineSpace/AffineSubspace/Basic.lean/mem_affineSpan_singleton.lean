import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P]

variable (k V) {p₁ p₂ : P}

theorem mem_affineSpan_singleton : p₁ ∈ affineSpan k ({p₂} : Set P) ↔ p₁ = p₂ := by
  simp [← mem_coe]

