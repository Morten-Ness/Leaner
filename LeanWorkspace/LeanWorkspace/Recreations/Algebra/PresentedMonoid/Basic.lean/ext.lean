import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  apply MonoidHom.eq_of_eqOn_denseM (PresentedMonoid.closure_range_of _)
  grind [Set.eqOn_range]

