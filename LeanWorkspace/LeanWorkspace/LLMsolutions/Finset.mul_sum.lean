import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem mul_sum (s : Finset ι) (f : ι → R) (a : R) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x s hx ih =>
      simp [hx, left_distrib, ih]
