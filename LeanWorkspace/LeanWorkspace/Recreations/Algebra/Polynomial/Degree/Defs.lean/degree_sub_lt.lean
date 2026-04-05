import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_sub_lt (hd : Polynomial.degree p = Polynomial.degree q) (hp0 : p ≠ 0)
    (hlc : Polynomial.leadingCoeff p = Polynomial.leadingCoeff q) : Polynomial.degree (p - q) < Polynomial.degree p := have hp : monomial (Polynomial.natDegree p) (Polynomial.leadingCoeff p) + p.erase (Polynomial.natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (Polynomial.natDegree q) (Polynomial.leadingCoeff q) + q.erase (Polynomial.natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : Polynomial.natDegree p = Polynomial.natDegree q := by unfold Polynomial.natDegree; rw [hd]
  have hq0 : q ≠ 0 := mt Polynomial.degree_eq_bot.2 (hd ▸ mt Polynomial.degree_eq_bot.1 hp0)
  calc
    Polynomial.degree (p - q) = Polynomial.degree (erase (Polynomial.natDegree q) p + -erase (Polynomial.natDegree q) q) := by
      conv =>
        lhs
        rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (Polynomial.degree (erase (Polynomial.natDegree q) p)) (Polynomial.degree (erase (Polynomial.natDegree q) q)) :=
      (Polynomial.degree_neg (erase (Polynomial.natDegree q) q) ▸ Polynomial.degree_add_le _ _)
    _ < Polynomial.degree p := max_lt_iff.2 ⟨hd' ▸ Polynomial.degree_erase_lt hp0, hd.symm ▸ Polynomial.degree_erase_lt hq0⟩

