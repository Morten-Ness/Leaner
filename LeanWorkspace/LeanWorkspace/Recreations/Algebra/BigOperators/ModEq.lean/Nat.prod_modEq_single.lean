import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

