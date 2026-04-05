import Mathlib

variable {M A B : Type*}

variable {α : Type*}

theorem closure_range_of : closure (Set.range <| @of α) = ⊤ := eq_top_iff.2 fun x _ =>
    FreeMonoid.recOn x (one_mem _) fun _x _xs hxs =>
      mul_mem (subset_closure <| Set.mem_range_self _) hxs

