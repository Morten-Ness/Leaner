import Mathlib

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

theorem schwartz_zippel_sum_degreeOf {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (S : Fin n → Finset R) :
    #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0) := by
  calc
    _ ≤ p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0) := MvPolynomial.schwartz_zippel_sup_sum hp S
    _ ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0) := Finset.sup_le fun s hs ↦ by
      gcongr with i; exact monomial_le_degreeOf i hs

