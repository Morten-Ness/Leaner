import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  nontriviality R
  have : (p.comp q).natDegree = p.natDegree * q.natDegree :=
    natDegree_comp_eq_of_mul_ne_zero <| by simp [hp.leadingCoeff, hq.leadingCoeff]
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, this, coeff_comp_degree_mul_degree h, hp.leadingCoeff,
    hq.leadingCoeff, one_pow, mul_one]

