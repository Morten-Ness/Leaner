import Mathlib

variable {ι : Type*}

theorem even_sum_iff_even_card_odd {s : Finset ι} (f : ι → ℕ) :
    Even (∑ i ∈ s, f i) ↔ Even #{x ∈ s | Odd (f x)} := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x ↦ Even (f x)), Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [Nat.even_iff, Finset.sum_nat_mod, Finset.sum_filter]
  simp +contextual only [Nat.not_even_iff_odd, Nat.odd_iff.mp]
  simp_rw [← Finset.sum_filter, ← Nat.even_iff, Finset.card_eq_sum_ones]

