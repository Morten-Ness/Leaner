import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_pair_le_of_mem_of_mem {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : line[k, p₁, p₂] ≤ s := by
  rw [affineSpan_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp₁, hp₂⟩

