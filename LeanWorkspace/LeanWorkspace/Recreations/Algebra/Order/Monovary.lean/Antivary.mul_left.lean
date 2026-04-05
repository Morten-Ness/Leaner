import Mathlib

variable {ι α β : Type*}

variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem Antivary.mul_left (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) : Antivary (f₁ * f₂) g := fun _i _j hij ↦ mul_le_mul' (h₁ hij) (h₂ hij)

