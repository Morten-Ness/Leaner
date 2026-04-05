import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem charP_zero_iff_charZero : CharP R 0 ↔ CharZero R := ⟨fun _ ↦ CharP.charP_to_charZero R, fun _ ↦ ofCharZero R⟩

