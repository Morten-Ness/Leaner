import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

