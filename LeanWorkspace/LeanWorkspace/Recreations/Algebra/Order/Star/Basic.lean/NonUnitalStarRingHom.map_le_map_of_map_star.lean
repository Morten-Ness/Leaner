import Mathlib

open scoped NNRat

variable {R A : Type*}

variable {F R S : Type*} [NonUnitalSemiring R] [PartialOrder R] [StarRing R]
  [StarOrderedRing R]

variable [NonUnitalSemiring S] [PartialOrder S] [StarRing S] [StarOrderedRing S]

theorem NonUnitalStarRingHom.map_le_map_of_map_star (f : R →⋆ₙ+* S) {x y : R} (hxy : x ≤ y) :
    f x ≤ f y := by
  rw [StarOrderedRing.le_iff] at hxy ⊢
  obtain ⟨p, hp, rfl⟩ := hxy
  refine ⟨f p, ?_, map_add f _ _⟩
  have hf : ∀ r, f (star r) = star (f r) := map_star _
  induction hp using AddSubmonoid.closure_induction
  all_goals aesop

