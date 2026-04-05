import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_add (f : ℕ → M) (n m : ℕ) :
    (∏ x ∈ range (n + m), f x) = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, Finset.prod_range_succ, Finset.prod_range_succ, hm, mul_assoc]

