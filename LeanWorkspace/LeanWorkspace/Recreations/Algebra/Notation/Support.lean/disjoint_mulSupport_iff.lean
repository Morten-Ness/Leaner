import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem disjoint_mulSupport_iff : Disjoint s (Function.mulSupport f) ↔ EqOn f 1 s := by
  rw [disjoint_comm, Function.mulSupport_disjoint_iff]

