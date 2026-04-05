FAIL
import Mathlib

variable (R : Type u)

variable [Ring R]

theorem free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (ModuleCat.free R).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (f x) := by
  simp [ModuleCat.freeMk]
