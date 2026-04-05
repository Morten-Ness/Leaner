import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem affineSpan_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s := by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact AffineSubspace.vadd_mem_of_mem_direction hv hp₁

