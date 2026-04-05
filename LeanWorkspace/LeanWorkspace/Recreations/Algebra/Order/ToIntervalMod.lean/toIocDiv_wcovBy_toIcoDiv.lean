import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_wcovBy_toIcoDiv (a b : α) : toIocDiv hp a b ⩿ toIcoDiv hp a b := by
  suffices toIocDiv hp a b = toIcoDiv hp a b ∨ toIocDiv hp a b + 1 = toIcoDiv hp a b by
    rwa [wcovBy_iff_eq_or_covBy, ← Order.succ_eq_iff_covBy]
  rw [eq_comm, ← AddCommGroup.not_modEq_iff_toIcoDiv_eq_toIocDiv, eq_comm, ←
    AddCommGroup.modEq_iff_toIcoDiv_eq_toIocDiv_add_one]
  exact em' _

