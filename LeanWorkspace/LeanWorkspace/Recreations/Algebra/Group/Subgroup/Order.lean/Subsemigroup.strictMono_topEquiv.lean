import Mathlib

theorem Subsemigroup.strictMono_topEquiv {G : Type*} [CommMonoid G] [Preorder G] :
    StrictMono (topEquiv (M := G)) := fun _ _ ↦ id

