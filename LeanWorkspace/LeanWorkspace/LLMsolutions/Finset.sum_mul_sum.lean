FAIL
import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, add_mul, Finset.mul_sum, ih, Finset.sum_add_distrib]
