import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ ∈ line[k, p₃, p₄])
    (h₂ : p₂ ∈ line[k, p₃, p₄]) : Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁),
    collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _

