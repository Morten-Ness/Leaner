import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {f : α → R} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∏ᶠ x, f x := finprod_induction (fun x => 0 ≤ x) zero_le_one (fun _ _ => mul_nonneg) hf

