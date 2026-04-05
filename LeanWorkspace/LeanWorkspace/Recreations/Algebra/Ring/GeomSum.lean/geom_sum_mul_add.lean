import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum_mul_add (x : R) (n : ℕ) : (∑ i ∈ range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

protected lemma Commute.geom_sum₂_comm (n : ℕ) (h : Commute x y) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using h.pow_pow _ _

-- TODO: for consistency, the next two lemmas should be moved to the root namespace

