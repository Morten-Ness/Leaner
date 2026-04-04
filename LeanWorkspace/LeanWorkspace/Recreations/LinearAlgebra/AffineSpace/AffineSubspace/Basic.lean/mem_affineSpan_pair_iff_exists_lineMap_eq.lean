import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem mem_affineSpan_pair_iff_exists_lineMap_eq {p p₁ p₂ : P} :
    p ∈ line[k, p₁, p₂] ↔ ∃ r : k, AffineMap.lineMap p₁ p₂ r = p := by
  constructor
  · intro h
    rw [← vsub_vadd p p₁, vadd_left_mem_affineSpan_pair] at h
    obtain ⟨r, hr⟩ := h
    refine ⟨r, ?_⟩
    rw [← vsub_vadd p p₁, ← hr, AffineMap.lineMap_apply]
  · rintro ⟨r, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

