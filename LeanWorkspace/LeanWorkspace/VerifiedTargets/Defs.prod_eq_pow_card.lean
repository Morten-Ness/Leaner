import Mathlib

variable {ι M N : Type*}

variable [Monoid M] [Monoid N]

theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.prod = m ^ l.length := by
  rw [← List.prod_replicate, ← List.eq_replicate_iff.mpr ⟨rfl, h⟩]

