import Mathlib

variable {ι α β γ : Type*}

variable {s : Finset ι}

theorem Int.finsetGcd_nonneg {f : ι → ℤ} : 0 ≤ s.gcd f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [Finset.gcd_insert, ha, ih, Int.gcd_nonneg]
