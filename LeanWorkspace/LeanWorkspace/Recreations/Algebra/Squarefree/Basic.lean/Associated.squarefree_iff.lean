import Mathlib

variable {R : Type*}

theorem Associated.squarefree_iff [Monoid R] {x y : R} (h : Associated x y) :
    Squarefree x ↔ Squarefree y := ⟨fun hx ↦ hx.squarefree_of_dvd h.dvd', fun hy ↦ hy.squarefree_of_dvd h.dvd⟩

