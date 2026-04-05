import Mathlib

variable {α G M : Type*}

variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

theorem prod_Ioc_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ioc m n, f i) * ∏ i ∈ Ioc n k, f i) = ∏ i ∈ Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intro x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

