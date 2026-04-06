FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_surjective : Function.Surjective (MonoidWithZeroHom.fst G₀ H₀) := by
  intro f
  refine ⟨
    { toFun := fun x => (f x, 1)
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp } ,
    rfl
  ⟩
