import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.injective [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) : Function.Injective p := by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha
  by_contra hij'
  refine ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr ?_)
  simp_all only [ne_eq]

