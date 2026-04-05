import Mathlib

section

variable {K : Type*} [Field K]

theorem gcd_eq [DecidableEq K] (a b : K) :
    EuclideanDomain.gcd a b = if a = 0 then b else a := by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]

end
