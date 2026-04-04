import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_triple_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ ∈ line[k, p₄, p₅])
    (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  refine (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

