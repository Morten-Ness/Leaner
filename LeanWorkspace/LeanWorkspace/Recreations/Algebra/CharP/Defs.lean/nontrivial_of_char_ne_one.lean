import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R := ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

