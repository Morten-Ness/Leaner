import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable [MulOneClass N]

theorem eqOn_closureM {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (Submonoid.closure s) := by
  let S : Submonoid M :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change f (a * b) = g (a * b)
        rw [map_mul, map_mul, ha, hb] }
  have hs : s ⊆ S := by
    intro x hx
    exact h hx
  have hclosure : Submonoid.closure s ≤ S := Submonoid.closure_le.2 hs
  intro x hx
  exact hclosure hx
