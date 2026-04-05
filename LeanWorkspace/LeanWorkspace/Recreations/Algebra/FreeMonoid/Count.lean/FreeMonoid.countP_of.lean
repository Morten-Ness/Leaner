import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP_of (x : α) : (of x).countP p =
    if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
  rw [FreeMonoid.countP_apply, toList_of, List.countP_singleton, apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]

