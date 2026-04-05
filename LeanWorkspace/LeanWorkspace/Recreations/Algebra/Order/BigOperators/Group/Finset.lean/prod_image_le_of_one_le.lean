import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

variable {ι' : Type*} [DecidableEq ι']

theorem prod_image_le_of_one_le [MulLeftMono N]
    {g : ι → ι'} {f : ι' → N} (hf : ∀ u ∈ s.image g, 1 ≤ f u) :
    ∏ u ∈ s.image g, f u ≤ ∏ u ∈ s, f (g u) := by
  rw [prod_comp f g]
  refine Finset.prod_le_prod' fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  apply le_self_pow (hf a hag)
  rw [← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

