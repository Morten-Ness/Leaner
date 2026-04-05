import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem count_of [DecidableEq α] (x y : α) :
    FreeMonoid.count x (of y) = Pi.mulSingle (M := fun _ ↦ Multiplicative ℕ) x (Multiplicative.ofAdd 1) y := by
  simp [FreeMonoid.count, FreeMonoid.countP_of, Pi.mulSingle_apply]

