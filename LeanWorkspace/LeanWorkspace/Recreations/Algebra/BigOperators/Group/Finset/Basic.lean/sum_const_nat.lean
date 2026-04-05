import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem sum_const_nat {m : ℕ} {f : ι → ℕ} (h₁ : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁

