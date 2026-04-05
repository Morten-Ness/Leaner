import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

theorem finsuppAntidiag_empty (n : μ) :
    Finset.finsuppAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by split_ifs with hn <;> simp [*]

