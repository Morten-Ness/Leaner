import Mathlib

variable {ι α β γ : Type*}

variable {s : Finset ι}

theorem Int.finsetGcd_nonneg {f : ι → ℤ} : 0 ≤ s.gcd f := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.gcd_cons, ← Int.coe_gcd]
    grind

