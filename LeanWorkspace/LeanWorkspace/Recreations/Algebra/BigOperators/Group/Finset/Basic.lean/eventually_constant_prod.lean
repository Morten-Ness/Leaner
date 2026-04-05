import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem eventually_constant_prod {u : ℕ → M} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k ∈ range n, u k) = ∏ k ∈ range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, Finset.prod_range_succ, hm, hu]

