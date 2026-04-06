FAIL
import Mathlib

variable {α β : Type*} [Neg α]

theorem Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro x
  rw [Pi.add_apply, hf x, hg x, Pi.neg_apply, add_comm]
