import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_map {α₁ : Type*} {g : α₁ → α} {x : FreeMonoid α₁} :
    FreeMonoid.map f (FreeMonoid.map g x) = FreeMonoid.map (f ∘ g) x := by
  unfold FreeMonoid.map
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, FreeMonoid.toList_ofList, List.map_map]

