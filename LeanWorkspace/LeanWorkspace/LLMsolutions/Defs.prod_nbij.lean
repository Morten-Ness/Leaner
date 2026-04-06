FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

theorem prod_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : (s : Set ι).InjOn i)
    (i_surj : (s : Set ι).SurjOn i t) (h : ∀ a ∈ s, f a = g (i a)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  classical
  classical
  rw [show ∏ x ∈ s, f x = ∏ x in s.image i, g x by
    refine Finset.prod_bij ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact i a
    · intro a ha
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · intro a ha
      exact h a ha
    · intro a₁ a₂ ha₁ ha₂ heq
      exact i_inj ha₁ ha₂ heq
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩]
  refine Finset.prod_subset ?_ ?_
  · intro x hx
    rcases i_surj hx with ⟨a, ha, rfl⟩
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · intro x hx ht
    exfalso
    exact ht (by
      rcases i_surj hx with ⟨a, ha, rfl⟩
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩)
