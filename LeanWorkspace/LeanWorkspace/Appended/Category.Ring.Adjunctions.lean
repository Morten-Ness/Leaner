import Mathlib

section

theorem free_obj_coe {α : Type u} : (CommRingCat.free.obj α : Type u) = MvPolynomial α ℤ := rfl

-- This is not a `@[simp]` lemma as the left-hand side simplifies via `dsimp`.

end
