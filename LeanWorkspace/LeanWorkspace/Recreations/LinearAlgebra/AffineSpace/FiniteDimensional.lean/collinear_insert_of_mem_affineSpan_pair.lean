import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair _ _ _

