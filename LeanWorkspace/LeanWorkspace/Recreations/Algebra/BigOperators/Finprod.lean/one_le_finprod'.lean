import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem one_le_finprod' {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i := finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

