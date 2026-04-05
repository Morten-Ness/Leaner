import Mathlib

variable (R : Type*)

theorem ringChar.eq_iff ringExpChar [Ring R] [IsDomain R] {q : ℕ} : ringExpChar R = q ↔ ExpChar R q := ⟨ringChar.of_eq ringExpChar, fun _ ↦ CharP.eq ringExpChar R q⟩

