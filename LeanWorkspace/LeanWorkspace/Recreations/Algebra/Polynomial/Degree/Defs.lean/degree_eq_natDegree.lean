import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_eq_natDegree (hp : p ≠ 0) : Polynomial.degree p = (Polynomial.natDegree p : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt Polynomial.degree_eq_bot.1 hp))
  have hn : Polynomial.degree p = some n := Classical.not_not.1 hn
  rw [Polynomial.natDegree, hn]; rfl

