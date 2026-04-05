import Mathlib

variable {α M G : Type*}

theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (Function.mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

