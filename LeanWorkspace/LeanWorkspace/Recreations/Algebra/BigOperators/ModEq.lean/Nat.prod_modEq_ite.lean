import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf

