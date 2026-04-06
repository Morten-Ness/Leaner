import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p ∈ s) : AffineSubspace.mk' p s.direction = s := by
  ext q
  change q -ᵥ p ∈ s.direction ↔ q ∈ s
  constructor
  · intro hq
    have hqp : q = (q -ᵥ p) +ᵥ p := by simpa using (vsub_vadd q p)
    rw [hqp]
    exact s.vadd_mem_of_mem_direction hq hp
  · intro hq
    exact s.vsub_mem_direction hq hp
