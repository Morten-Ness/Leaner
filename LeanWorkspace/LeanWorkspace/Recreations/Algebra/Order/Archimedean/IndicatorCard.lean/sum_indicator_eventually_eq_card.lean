import Mathlib

theorem sum_indicator_eventually_eq_card {α : Type*} [AddCommMonoid α] (a : α) {s : Set ℕ}
    (hs : s.Finite) :
    ∀ᶠ n in atTop, ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ a) k = (Nat.card s) • a := by
  have key : ∀ x ∈ hs.toFinset, s.indicator (fun _ ↦ a) x = a := by
    intro x hx
    rw [indicator_of_mem (hs.mem_toFinset.1 hx) (fun _ ↦ a)]
  rw [Nat.card_eq_card_finite_toFinset hs, ← sum_eq_card_nsmul key, eventually_atTop]
  obtain ⟨m, hm⟩ := hs.bddAbove
  refine ⟨m + 1, fun n n_m ↦ (sum_subset ?_ ?_).symm⟩ <;> intro x <;> rw [hs.mem_toFinset]
  · rw [Finset.mem_range]
    exact fun x_s ↦ ((mem_upperBounds.1 hm) x x_s).trans_lt (Nat.lt_of_succ_le n_m)
  · exact fun _ x_s ↦ indicator_of_notMem x_s (fun _ ↦ a)

