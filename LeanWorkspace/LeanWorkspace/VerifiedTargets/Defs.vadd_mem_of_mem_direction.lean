import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s := by
  rw [AffineSubspace.mem_direction_iff_eq_vsub ⟨p, hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

