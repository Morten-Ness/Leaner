import Mathlib

variable {α : Type u} {β : Type v}

theorem length_toFreeSemigroup (x : FreeMagma α) : (FreeMagma.toFreeSemigroup x).length = x.length := FreeMagma.recOnMul x (fun _ ↦ rfl) fun x y hx hy ↦ by
    rw [map_mul, FreeSemigroup.length_mul, hx, hy]; rfl

