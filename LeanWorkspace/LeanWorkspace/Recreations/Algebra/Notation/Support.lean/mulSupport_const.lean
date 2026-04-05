import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_const {c : M} (hc : c ≠ 1) : (Function.mulSupport fun _ : ι ↦ c) = Set.univ := by
  ext x; simp [hc]

