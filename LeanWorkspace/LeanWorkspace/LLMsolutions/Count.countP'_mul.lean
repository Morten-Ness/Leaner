FAIL
import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP'_mul (l₁ l₂ : FreeMonoid α) : (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p := by
  induction l₁ using FreeMonoid.recOn with
  | hnil =>
      simp [FreeMonoid.countP']
  | hcons a l ih =>
      by_cases h : p a
      · simp [FreeMonoid.countP', h, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [FreeMonoid.countP', h, ih]
