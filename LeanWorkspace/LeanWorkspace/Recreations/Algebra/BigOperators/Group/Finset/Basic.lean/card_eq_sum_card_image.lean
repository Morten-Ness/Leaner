import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem card_eq_sum_card_image [DecidableEq M] (f : ι → M) (s : Finset ι) :
    #s = ∑ b ∈ s.image f, #{a ∈ s | f a = b} := Finset.card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

