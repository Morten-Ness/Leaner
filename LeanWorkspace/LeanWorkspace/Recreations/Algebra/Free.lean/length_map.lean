import Mathlib

variable {α : Type u}

variable {β : Type v} (f : α → β)

theorem length_map (x) : (FreeSemigroup.map f x).length = x.length := FreeSemigroup.recOnMul x (fun _ ↦ rfl) (fun x y hx hy ↦ by simp only [map_mul, FreeSemigroup.length_mul, *])

