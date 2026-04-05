import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

theorem surjective_mk {rels : FreeMonoid α → FreeMonoid α → Prop} :
    Function.Surjective (PresentedMonoid.mk rels) := fun x ↦ PresentedMonoid.inductionOn x fun a ↦ .intro a rfl

