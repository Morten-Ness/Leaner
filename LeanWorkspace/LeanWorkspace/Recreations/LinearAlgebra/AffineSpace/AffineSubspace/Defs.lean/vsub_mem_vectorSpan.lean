import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    p₁ -ᵥ p₂ ∈ vectorSpan k s := vsub_set_subset_vectorSpan k s (vsub_mem_vsub hp₁ hp₂)

