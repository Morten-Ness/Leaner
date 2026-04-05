import Mathlib

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : ℕ × ℕ → M)
    (n : ℕ) : ∏ ij ∈ antidiagonal n, f ij = ∏ k ∈ range n.succ, f (k, n - k) := Finset.prod_map (range n.succ) ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.mk.inj h).1⟩ f

