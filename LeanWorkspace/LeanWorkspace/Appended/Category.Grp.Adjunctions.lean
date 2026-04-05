import Mathlib

section

theorem free_obj_coe {α : Type u} : (AddCommGrpCat.free.obj α : Type u) = FreeAbelianGroup α := rfl

-- This currently can't be a `simp` lemma,
-- because `free_obj_coe` will simplify implicit arguments in the LHS.
-- (The `simpNF` linter will, correctly, complain.)

end
