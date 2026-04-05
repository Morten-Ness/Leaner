import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf

