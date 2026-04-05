import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v ∈ s.direction ↔ ∃ p₁ ∈ s, ∃ p₂ ∈ s, v = p₁ -ᵥ p₂ := by
  rw [← SetLike.mem_coe, AffineSubspace.coe_direction_eq_vsub_set h, Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

