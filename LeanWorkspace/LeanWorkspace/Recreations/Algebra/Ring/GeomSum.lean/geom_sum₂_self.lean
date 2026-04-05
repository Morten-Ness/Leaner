import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum₂_self (x : R) (n : ℕ) : ∑ i ∈ range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) := calc
    ∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i ∈ Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| Finset.mem_range.1 hi
    _ = #(range n) • x ^ (n - 1) := Finset.sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]

