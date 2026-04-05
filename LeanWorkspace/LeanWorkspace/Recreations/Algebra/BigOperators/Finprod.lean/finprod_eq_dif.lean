import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_dif {p : Prop} [Decidable p] (f : p → M) :
    ∏ᶠ i, f i = if h : p then f h else 1 := by
  split_ifs with h
  · haveI : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · haveI : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f

