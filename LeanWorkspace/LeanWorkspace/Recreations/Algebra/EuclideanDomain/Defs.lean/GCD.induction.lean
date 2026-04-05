import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem GCD.induction {P : R → R → Prop} (a b : R) (H0 : ∀ x, P 0 x)
    (H1 : ∀ a b, a ≠ 0 → P (b % a) a → P a b) : P a b := by
  classical
  exact if a0 : a = 0 then
    a0.symm ▸ H0 b
  else
    have _ := EuclideanDomain.mod_lt b a0
    H1 _ _ a0 (GCD.induction (b % a) a H0 H1)
termination_by a

