import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
    [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i := finprod_induction _ le_rfl (fun _ _ ↦ one_le_mul_of_one_le_of_one_le) hf

