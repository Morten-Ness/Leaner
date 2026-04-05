import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

variable {s : Finset ι} {n : μ} {f : ι → μ}

theorem piAntidiag_empty (n : μ) : Finset.piAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn <;> simp [*]

