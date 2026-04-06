FAIL
import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable [Mul N]

theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subsemigroup.closure s) := by
  intro x hx
  let S : Subsemigroup M := Subsemigroup.mk (Set.EqOn f g (Subsemigroup.closure s)) ?_
  · exact S.property hx
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [f.map_mul, g.map_mul, ha, hb]
  · refine Subsemigroup.closure_le.2 ?_
    intro y hy
    exact h hy
