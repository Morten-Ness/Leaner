import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Ring R] [AddCommGroup M]

variable {module_M : Module R M}

variable (p p' : Submodule R M)

variable {r : R} {x y : M}

theorem sub_mem_iff_left (hy : y ∈ p) : x - y ∈ p ↔ x ∈ p := by
  rw [sub_eq_add_neg, Submodule.add_mem_iff_left p (Submodule.neg_mem p hy)]

