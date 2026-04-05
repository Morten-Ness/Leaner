import Mathlib

open scoped Pointwise

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem card_support_mul_le : #(p * q).support ≤ #p.support * #q.support := by
  calc #(p * q).support
    _ = #(p.toFinsupp * q.toFinsupp).support := by rw [← support_toFinsupp, toFinsupp_mul]
    _ ≤ #(p.toFinsupp.support + q.toFinsupp.support) :=
      Finset.card_le_card (AddMonoidAlgebra.support_mul p.toFinsupp q.toFinsupp)
    _ ≤ #p.support * #q.support := Finset.card_image₂_le ..

