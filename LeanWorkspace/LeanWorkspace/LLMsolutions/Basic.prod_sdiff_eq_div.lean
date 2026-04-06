FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) : ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [div_eq_mul_inv]
  symm
  simpa using (Finset.prod_sdiff (β := G) h f)
