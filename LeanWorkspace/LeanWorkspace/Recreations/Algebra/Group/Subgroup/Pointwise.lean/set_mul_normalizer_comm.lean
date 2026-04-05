import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem set_mul_normalizer_comm (S : Set G) (N : Subgroup G) (hLE : S ⊆ normalizer (N : Set G)) :
    S * N = N * S := by
  rw [← iUnion_mul_left_image, ← iUnion_mul_right_image]
  simp only [image_mul_left, image_mul_right, Set.preimage]
  congr! 5 with s hs x
  exact (mem_normalizer_iff'.mp (inv_mem (hLE hs)) x).symm

