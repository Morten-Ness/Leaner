import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_insert_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄, p₅} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1
        (affineSpan_mono k ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) _ h₁),
    collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₂),
    collinear_insert_iff_of_mem_affineSpan h₃]
  exact collinear_pair _ _ _

