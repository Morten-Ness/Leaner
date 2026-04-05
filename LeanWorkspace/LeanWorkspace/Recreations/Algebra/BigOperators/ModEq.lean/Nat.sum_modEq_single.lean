import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

