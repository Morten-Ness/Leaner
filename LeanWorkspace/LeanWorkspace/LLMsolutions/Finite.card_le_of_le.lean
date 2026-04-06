FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_of_le {H K : Subgroup G} [Finite K] (h : H ≤ K) : Nat.card H ≤ Nat.card K := by
  classical
  let f : H → K := fun x => ⟨x.1, h x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext <| Subtype.mk.inj hxy
  letI : Finite H := Finite.of_injective f hf
  let eH : Fintype H := Fintype.ofFinite H
  let eK : Fintype K := Fintype.ofFinite K
  exact Fintype.card_le_of_injective f hf
