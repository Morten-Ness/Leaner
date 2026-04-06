import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_top : Nat.card (⊤ : Subgroup G) = Nat.card G := by
  let e : (⊤ : Subgroup G) ≃ G :=
    { toFun := fun x => x.1
      invFun := fun g => ⟨g, by trivial⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro g
        rfl }
  exact Nat.card_congr e
