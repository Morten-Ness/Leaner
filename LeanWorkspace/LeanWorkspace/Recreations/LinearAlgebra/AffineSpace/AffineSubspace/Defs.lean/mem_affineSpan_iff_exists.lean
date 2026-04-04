import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem mem_affineSpan_iff_exists {p : P} {s : Set P} : p ∈ affineSpan k s ↔
    ∃ p₁ ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p₁ := Iff.rfl

