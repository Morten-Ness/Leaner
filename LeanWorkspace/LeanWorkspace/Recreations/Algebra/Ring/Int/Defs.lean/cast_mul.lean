import Mathlib

theorem cast_mul {α : Type*} [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]

