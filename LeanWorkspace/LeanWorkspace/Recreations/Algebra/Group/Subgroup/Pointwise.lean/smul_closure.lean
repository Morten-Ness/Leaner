import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem smul_closure (a : α) (s : Set G) : a • closure s = closure (a • s) := MonoidHom.map_closure _ _

