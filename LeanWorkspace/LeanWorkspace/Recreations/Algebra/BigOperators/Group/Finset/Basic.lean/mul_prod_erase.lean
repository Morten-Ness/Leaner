import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem mul_prod_erase [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  rw [← Finset.prod_insert (notMem_erase a s), insert_erase h]

