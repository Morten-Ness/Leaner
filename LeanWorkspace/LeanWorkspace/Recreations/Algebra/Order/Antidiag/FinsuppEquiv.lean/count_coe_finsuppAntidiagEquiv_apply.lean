import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ}

theorem count_coe_finsuppAntidiagEquiv_apply (n : ℕ) (f : s.finsuppAntidiag n) (a : s) :
    (Finset.finsuppAntidiagEquiv s n f).toMultiset.count a = f.val a := by
  simp [Finset.finsuppAntidiagEquiv]

