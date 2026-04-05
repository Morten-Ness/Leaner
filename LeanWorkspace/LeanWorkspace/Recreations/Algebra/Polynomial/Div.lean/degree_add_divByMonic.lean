import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_add_divByMonic (hq : Polynomial.Monic q) (h : degree q ≤ degree p) :
    degree q + degree (p /ₘ q) = degree p := by
  nontriviality R
  have hdiv0 : p /ₘ q ≠ 0 := by rwa [Ne, Polynomial.divByMonic_eq_zero_iff hq, not_lt]
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) ≠ 0 := by
    rwa [Polynomial.Monic.def.1 hq, one_mul, Ne, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree (p %ₘ q) < degree q := Polynomial.degree_modByMonic_lt _ hq
      _ ≤ _ := by
        rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hdiv0, ←
            Nat.cast_add, Nat.cast_le]
        exact Nat.le_add_right _ _
  calc
    degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) := Eq.symm (degree_mul' hlc)
    _ = degree (p %ₘ q + q * (p /ₘ q)) := (Polynomial.degree_add_eq_right_of_degree_lt hmod).symm
    _ = _ := congr_arg _ (Polynomial.modByMonic_add_div _ _)

