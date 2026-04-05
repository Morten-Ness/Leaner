import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n := Nat.recOn n (by simp) fun n ih h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ', pow_succ', Polynomial.leadingCoeff_mul' h₂, ih h₁]

