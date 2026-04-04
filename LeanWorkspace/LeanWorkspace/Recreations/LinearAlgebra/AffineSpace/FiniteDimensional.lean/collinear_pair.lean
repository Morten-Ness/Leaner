import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · use 0
    simp [hp]
  · use 1
    simp [hp]

