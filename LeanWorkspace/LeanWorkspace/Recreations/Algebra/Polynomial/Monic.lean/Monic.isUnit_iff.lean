import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.isUnit_iff (hm : p.Monic) : IsUnit p ↔ p = 1 := ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩

