import Mathlib

variable {S M G : Type*}

theorem semiconjBy_iff_eq [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x = y := ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩

