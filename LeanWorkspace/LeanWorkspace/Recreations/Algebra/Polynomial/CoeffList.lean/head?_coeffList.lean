import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem head?_coeffList (h : P ≠ 0) :
    P.coeffList.head? = P.leadingCoeff := (Polynomial.coeffList_eq_cons_leadingCoeff h).casesOn fun _ ↦ (Eq.symm · ▸ rfl)

