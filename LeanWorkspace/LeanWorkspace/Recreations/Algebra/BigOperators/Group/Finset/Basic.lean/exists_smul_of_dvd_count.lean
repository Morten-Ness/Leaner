import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem exists_smul_of_dvd_count (s : Multiset ι) {k : ℕ}
    (h : ∀ a : ι, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset ι, s = k • u := by
  use ∑ a ∈ s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x ∈ s.toFinset, k • (count x s / k) • ({x} : Multiset ι)) =
      ∑ x ∈ s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, Multiset.toFinset_sum_count_nsmul_eq]

