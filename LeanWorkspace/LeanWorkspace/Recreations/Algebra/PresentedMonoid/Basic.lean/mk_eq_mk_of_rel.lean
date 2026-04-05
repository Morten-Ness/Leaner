import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

theorem mk_eq_mk_of_rel (h : rels x y) : PresentedMonoid.mk rels x = PresentedMonoid.mk rels y := PresentedMonoid.mk_eq_mk_iff.2 (.of _ _ h)

