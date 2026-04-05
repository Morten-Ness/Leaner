import Mathlib

variable {R : Type*} {a b : R}

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι → R}

theorem IsRegular.prod (h : ∀ i ∈ s, IsRegular (f i)) :
    IsRegular (∏ i ∈ s, f i) := ⟨IsLeftRegular.prod fun a ha ↦ (h a ha).left,
   IsRightRegular.prod fun a ha ↦ (h a ha).right⟩

