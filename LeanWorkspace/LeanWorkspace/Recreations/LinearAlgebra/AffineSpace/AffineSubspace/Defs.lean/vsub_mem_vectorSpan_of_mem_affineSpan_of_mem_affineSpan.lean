import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k}

theorem vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ affineSpan k s) (hp₂ : p₂ ∈ affineSpan k s) : p₁ -ᵥ p₂ ∈ vectorSpan k s := vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂

