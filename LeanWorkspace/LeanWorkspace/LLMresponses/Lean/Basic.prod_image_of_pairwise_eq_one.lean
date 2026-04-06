FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {I : Finset κ}
    (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simp
  | @insert a I ha hI =>
      have hf' : ((I : Set κ)).Pairwise fun i j ↦ f i = f j → g (f i) = 1 := by
        intro i hi j hj hne hij
        exact hf (by simp [hi]) (by simp [hj]) (by simpa using hne) hij
      by_cases hfa : f a ∈ I.image f
      · have hga : g (f a) = 1 := by
          rcases Finset.mem_image.mp hfa with ⟨b, hb, hfb⟩
          have hne' : a ≠ b := by
            intro h
            apply ha
            simpa [h] using hb
          exact hf (by simp) (by simp [hb]) hne' hfb.symm
        rw [Finset.image_insert]
        have hnot : ¬ f a ∉ I.image f := by simpa using hfa
        rw [Finset.prod_insert hnot]
        rw [hI hf']
        rw [Finset.prod_insert ha]
        simp [hga]
      · rw [Finset.image_insert]
        have hnot : f a ∉ I.image f := hfa
        rw [Finset.prod_insert hnot]
        rw [hI hf']
        rw [Finset.prod_insert ha]
        simp
