import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b := ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy, mul_comm, ← Units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_one] at hc
    exact hc, fun h => by rw [h]⟩

