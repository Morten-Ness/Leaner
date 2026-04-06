FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subfield.closure s) := by
  intro x hx
  let S : Subfield K :=
    { carrier := {x | f x = g x}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp [ha, hb, map_add]
      mul_mem' := by
        intro a b ha hb
        simp [ha, hb, map_mul]
      neg_mem' := by
        intro a ha
        simp [ha]
      inv_mem' := by
        intro a ha
        simp [ha, map_inv₀] }
  have hs : s ⊆ S := by
    intro y hy
    exact h hy
  have hclosure : Subfield.closure s ≤ S := Subfield.closure_le.2 hs
  exact hclosure hx
