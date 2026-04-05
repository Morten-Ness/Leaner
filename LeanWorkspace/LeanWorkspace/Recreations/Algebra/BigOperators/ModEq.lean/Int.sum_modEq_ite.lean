import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf

