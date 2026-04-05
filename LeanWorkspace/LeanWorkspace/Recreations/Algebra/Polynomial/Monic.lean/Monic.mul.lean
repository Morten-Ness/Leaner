import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.mul (hp : Polynomial.Monic p) (hq : Polynomial.Monic q) : Polynomial.Monic (p * q) := letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
      simp [Polynomial.Monic.def.1 hp, Polynomial.Monic.def.1 hq, Ne.symm h0]
    rw [Polynomial.Monic.def, leadingCoeff_mul' this, Polynomial.Monic.def.1 hp, Polynomial.Monic.def.1 hq, one_mul]

