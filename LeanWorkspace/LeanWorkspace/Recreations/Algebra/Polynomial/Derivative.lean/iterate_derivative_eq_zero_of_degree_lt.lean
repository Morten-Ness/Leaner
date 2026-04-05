import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem iterate_derivative_eq_zero_of_degree_lt {k : ℕ} {P : R[X]} (h : P.degree < k) :
    Polynomial.derivative^[k] P = 0 := by
  induction k generalizing P
  case zero => exact degree_eq_bot.mp <| WithBot.lt_coe_bot.mp h
  case succ k ind =>
    by_cases P = 0
    case pos hP => simp [hP]
    case neg hP =>
      rw [Function.iterate_add_apply, Function.iterate_one]
      by_cases Polynomial.derivative P = 0
      case pos hP' => simp [hP']
      case neg hP' =>
        have hP'' : P.natDegree ≠ 0 := by
          contrapose! hP'
          exact Polynomial.derivative_of_natDegree_zero hP'
        refine ind <| (natDegree_lt_iff_degree_lt hP').mp ?_
        linarith [(natDegree_lt_iff_degree_lt hP).mpr h, Polynomial.natDegree_derivative_lt hP'']

