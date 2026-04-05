import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem degree_divX_lt (hp0 : p ≠ 0) : (Polynomial.divX p).degree < p.degree := by
  haveI := Nontrivial.of_polynomial_ne hp0
  calc
    degree (Polynomial.divX p) < (Polynomial.divX p * Polynomial.X + Polynomial.C (p.coeff 0)).degree :=
      if h : degree p ≤ 0 then by
        have h' : Polynomial.C (p.coeff 0) ≠ 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h, Polynomial.divX_C, degree_zero, zero_mul, zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : Polynomial.divX p ≠ 0 := by
          simpa [Polynomial.divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (Polynomial.divX p) * leadingCoeff Polynomial.X ≠ 0 := by simpa
        have : degree (Polynomial.C (p.coeff 0)) < degree (Polynomial.divX p * Polynomial.X) :=
          calc
            degree (Polynomial.C (p.coeff 0)) ≤ 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (Polynomial.X : R[X]) := degree_X.symm
            _ ≤ degree (Polynomial.divX p * Polynomial.X) := by
              rw [← zero_add (degree Polynomial.X), degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, Polynomial.divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (Polynomial.divX_mul_X_add _)

