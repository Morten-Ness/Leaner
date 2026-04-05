import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

theorem mk_eq_mk_iff : PresentedMonoid.mk rels x = PresentedMonoid.mk rels y ↔ conGen rels x y := Quotient.eq

