import Mathlib

theorem MulEquiv.strictMono_subsemigroupCongr {G : Type*}
    [CommMonoid G] [Preorder G] {S T : Subsemigroup G}
    (h : S = T) : StrictMono (subsemigroupCongr h) := fun _ _ ↦ id

