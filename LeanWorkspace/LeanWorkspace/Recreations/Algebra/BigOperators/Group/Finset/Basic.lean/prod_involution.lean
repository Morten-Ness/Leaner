import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_involution (g : ∀ a ∈ s, ι) (hg₁ : ∀ a ha, f a * f (g a ha) = 1)
    (hg₃ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
    (g_mem : ∀ a ha, g a ha ∈ s) (hg₄ : ∀ a ha, g (g a ha) (g_mem a ha) = a) :
    ∏ x ∈ s, f x = 1 := by
  classical
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have : {x, g x hx} ⊆ s := by simp [insert_subset_iff, hx, g_mem]
  suffices h : ∏ x ∈ s \ {x, g x hx}, f x = 1 by
    rw [← Finset.prod_sdiff this, h, one_mul]
    cases eq_or_ne (g x hx) x with
    | inl hx' => simpa [hx'] using hg₃ x hx
    | inr hx' => grind
  suffices h₃ : ∀ a (ha : a ∈ s \ {x, g x hx}), g a (sdiff_subset ha) ∈ s \ {x, g x hx} from
    ih (s \ {x, g x hx}) (ssubset_iff.2 ⟨x, by simp [insert_subset_iff, hx]⟩) _
      (by simp [hg₁]) (fun _ _ => hg₃ _ _) h₃ (fun _ _ => hg₄ _ _)
  grind

