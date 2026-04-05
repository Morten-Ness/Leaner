import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

theorem of_abv_le (n : ℕ) (hm : ∀ m, n ≤ m → abv (f m) ≤ a m) :
    IsCauSeq abs (fun n ↦ ∑ i ∈ range n, a i) → IsCauSeq abv fun n ↦ ∑ i ∈ range n, f i := by
  intro hg ε ε0
  obtain ⟨i, hi⟩ := hg (ε / 2) (div_pos ε0 (by simp))
  exists max n i
  intro j ji
  have hi₁ := hi j (le_trans (le_max_right n i) ji)
  have hi₂ := hi (max n i) (le_max_right n i)
  have sub_le :=
    abs_sub_le (∑ k ∈ range j, a k) (∑ k ∈ range i, a k) (∑ k ∈ range (max n i), a k)
  have := add_lt_add hi₁ hi₂
  rw [abs_sub_comm (∑ k ∈ range (max n i), a k), add_halves ε] at this
  refine lt_of_le_of_lt (le_trans (le_trans ?_ (le_abs_self _)) sub_le) this
  generalize hk : j - max n i = k
  clear this hi₂ hi₁ hi ε0 ε hg sub_le
  rw [tsub_eq_iff_eq_add_of_le ji] at hk
  rw [hk]
  dsimp only
  clear hk ji j
  induction k with
  | zero => simp [abv_zero abv]
  | succ k hi =>
    simp only [Nat.succ_add, Nat.succ_eq_add_one, Finset.sum_range_succ_comm]
    simp only [add_assoc, sub_eq_add_neg]
    simp only [sub_eq_add_neg] at hi
    grw [abv_add abv, hm _ (by omega), hi]

