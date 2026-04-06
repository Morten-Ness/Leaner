FAIL
import Mathlib

variable (R : Type u)

variable [Ring R]

theorem free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (ModuleCat.free R).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (f x) := by
  ext y
  by_cases h : f x = y
  · subst h
    simp [ModuleCat.free, ModuleCat.freeMk]
  · simp [ModuleCat.free, ModuleCat.freeMk, Finsupp.lmapDomain_apply, h, Finsupp.single_apply]
