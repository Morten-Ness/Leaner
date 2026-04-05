import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem count_of [DecidableEq α] (x y : α) : FreeAddMonoid.count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  dsimp [FreeAddMonoid.count]
  rw [FreeAddMonoid.countP_of]
  simp [Pi.single, Function.update]

