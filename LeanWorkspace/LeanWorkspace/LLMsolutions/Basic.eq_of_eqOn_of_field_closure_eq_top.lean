FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : Subfield.closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g := by
  ext x
  have hx : x ∈ Subfield.closure s := by
    rw [hs]
    simp
  refine Subfield.closure_induction hx ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact h hy
  · simp
  · intro a b ha hb
    simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_mul, ha, hb]
  · intro a ha
    simp [map_inv₀, ha]
