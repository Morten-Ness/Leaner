import Mathlib

variable {ι α β M N G k R : Type*}

theorem sum_le_one_iff {s : Finset α} {f : α → ℕ} :
    ∑ x ∈ s, f x ≤ 1 ↔ ∀ x y, x ∈ s → y ∈ s → f x ≠ 0 → f y ≠ 0 → x = y ∧ f x = 1 := by
  classical
  refine ⟨fun h x y hsx hsy hfx hfy ↦ ?_, fun h ↦ ?_⟩
  · replace h := (sum_mono_set f (show {x, y} ⊆ s by grind)).trans h
    grind
  · by_cases! hx : ∃ x ∈ s, f x ≠ 0
    · obtain ⟨x, hsx, hfx⟩ := hx
      have hs : ∀ y ∈ s \ {x}, f y = 0 := by grind
      simp [← sum_sdiff (singleton_subset_iff.2 hsx), sum_congr rfl hs, (h x x hsx hsx hfx hfx).2]
    · simp [sum_congr rfl hx]

