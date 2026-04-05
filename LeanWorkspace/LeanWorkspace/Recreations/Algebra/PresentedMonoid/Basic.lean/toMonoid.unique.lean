import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

variable {α M : Type*} [Monoid M] (f : α → M)

variable {rels : FreeMonoid α → FreeMonoid α → Prop}

variable (h : ∀ a b : FreeMonoid α, rels a b → FreeMonoid.lift f a = FreeMonoid.lift f b)

theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : ∀ a : α, g (PresentedMonoid.of rels a) = f a) : g = PresentedMonoid.lift f h := Con.lift_unique (Con.conGen_le h) g (FreeMonoid.hom_eq hg)

