import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₁ -ᵥ p₂) := by
  simp_rw [vectorSpan_eq_span_vsub_set_left k (mem_insert p₁ _), image_pair, vsub_self,
    Submodule.span_insert_zero]

