import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem affineIndependent_of_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P}
    (ha : AffineIndependent k ![p₁, p₂, p₃]) (hcol : Collinear k {p₂, p₃, p}) (hne : p₂ ≠ p) :
    AffineIndependent k ![p₁, p₂, p] := by
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have h1 : Collinear k {p₁, p₃, p₂, p} := by
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hne
    · apply Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hne
  have h2 : Collinear k {p₁, p₂, p₃} := h1.subset (by grind)
  rw [affineIndependent_iff_not_collinear_set] at ha
  exact ha h2

