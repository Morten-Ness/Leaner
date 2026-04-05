import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem not_dvd_of_degree_lt (hp : Polynomial.Monic p) (h0 : q ≠ 0) (hl : degree q < degree p) : ¬p ∣ q := Polynomial.Monic.not_dvd_of_natDegree_lt hp h0 <| natDegree_lt_natDegree h0 hl

