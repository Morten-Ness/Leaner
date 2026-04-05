import Mathlib

theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) :
    (AddCommGrpCat.free.map f) x = f <$> x := rfl

