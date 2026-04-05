import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ}

theorem finsuppAntidiagEquiv_symm_apply_apply (n : ℕ) (f : Sym s n) (a : s) :
    ((Finset.finsuppAntidiagEquiv s n).symm f).val a.val = f.toMultiset.count a := by
  simp [Finset.finsuppAntidiagEquiv]

