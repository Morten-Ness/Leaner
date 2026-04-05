import Mathlib

variable (R : Type u) [Semiring R]

theorem id_apply (M : SemimoduleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

