import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : ((s₁ : Set P) ∩ s₂).Nonempty) : s₁ = s₂ := by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine AffineSubspace.vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact AffineSubspace.vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine AffineSubspace.vadd_mem_of_mem_direction ?_ hq1
    rw [hd]
    exact AffineSubspace.vsub_mem_direction hp hq2

