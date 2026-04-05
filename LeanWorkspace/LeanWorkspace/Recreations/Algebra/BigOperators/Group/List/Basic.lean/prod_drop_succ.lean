import Mathlib

variable {ι α β M N P G : Type*}

variable [Group G]

theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p : i < L.length), (L.drop (i + 1)).prod = L[i]⁻¹ * (L.drop i).prod
  | [], _, p => False.elim (Nat.not_lt_zero _ p)
  | _ :: _, 0, _ => by simp
  | _ :: xs, i + 1, p => prod_drop_succ xs i (Nat.lt_of_succ_lt_succ p)
