import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x := (ringChar.spec R x).1 hx

