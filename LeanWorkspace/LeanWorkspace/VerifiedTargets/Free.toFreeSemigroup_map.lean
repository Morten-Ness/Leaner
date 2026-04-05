import Mathlib

variable {α : Type u} {β : Type v}

theorem toFreeSemigroup_map (f : α → β) (x : FreeMagma α) :
    FreeMagma.toFreeSemigroup (FreeMagma.map f x) = FreeSemigroup.map f (FreeMagma.toFreeSemigroup x) := DFunLike.congr_fun (FreeMagma.toFreeSemigroup_comp_map f) x

