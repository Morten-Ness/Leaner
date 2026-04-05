import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ}

theorem card_finsuppAntidiag_nat_eq_choose (n : ℕ) :
    #(s.finsuppAntidiag n) = (#s + n - 1).choose n := by
  simp [card_eq_of_equiv_fintype (Finset.finsuppAntidiagEquiv s n), Sym.card_sym_eq_choose]

