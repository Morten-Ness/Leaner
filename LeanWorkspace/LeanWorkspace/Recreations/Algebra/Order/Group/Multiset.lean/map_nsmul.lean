import Mathlib

variable {α β : Type*}

theorem map_nsmul (f : α → β) (n : ℕ) (s) : map f (n • s) = n • map f s := (Multiset.mapAddMonoidHom f).map_nsmul _ _

