import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP_of (x : α) : FreeAddMonoid.countP p (of x) = if p x then 1 else 0 := by
  rw [FreeAddMonoid.countP_apply, toList_of, List.countP_singleton]
  simp only [decide_eq_true_eq]

