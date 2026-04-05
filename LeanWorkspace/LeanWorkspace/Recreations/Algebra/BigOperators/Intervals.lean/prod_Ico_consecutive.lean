import Mathlib

variable {α G M : Type*}

variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

theorem prod_Ico_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ico m n, f i) * ∏ i ∈ Ico n k, f i) = ∏ i ∈ Ico m k, f i := Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

