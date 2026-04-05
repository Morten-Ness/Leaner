import Mathlib

variable {ι α β M N P G : Type*}

variable [Group G]

theorem prod_rotate_eq_one_of_prod_eq_one :
    ∀ {l : List G} (_ : l.prod = 1) (n : ℕ), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl
    rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq,
      ← one_mul (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_cancel, mul_one]

