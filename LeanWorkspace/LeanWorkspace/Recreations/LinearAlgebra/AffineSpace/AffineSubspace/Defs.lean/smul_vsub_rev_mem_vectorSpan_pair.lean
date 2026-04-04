import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem smul_vsub_rev_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) ∈ vectorSpan k ({p₁, p₂} : Set P) := Submodule.smul_mem _ _ (vsub_rev_mem_vectorSpan_pair k p₁ p₂)

