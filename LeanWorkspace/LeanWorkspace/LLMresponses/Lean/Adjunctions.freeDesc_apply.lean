FAIL
import Mathlib

variable (R : Type u)

variable [Ring R]

theorem freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    ModuleCat.freeDesc f (ModuleCat.freeMk x) = f x := by
  rw [ModuleCat.freeDesc]
  change Finsupp.total X M R f (Finsupp.single x 1) = f x
  simp [Finsupp.total, Finsupp.lsum, DFinsupp.sumAddHom_single]
