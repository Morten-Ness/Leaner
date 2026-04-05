import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_ninvolution (g : ι → ι) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 := Finset.prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

