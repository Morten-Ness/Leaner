import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem not_dvd_of_natDegree_lt (hp : Polynomial.Monic p) (h0 : q ≠ 0) (hl : natDegree q < natDegree p) :
    ¬p ∣ q := by
  rintro ⟨r, rfl⟩
  rw [hp.natDegree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_ge (Nat.le_add_right _ _)

