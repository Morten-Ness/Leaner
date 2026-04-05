import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem prev_f_of_not_boundaryGE [e.IsRelIff] {i j : ι} (hij : c.prev j = i)
    (hj : ¬ e.BoundaryGE j) :
    c'.prev (e.f j) = e.f i := by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [ComplexShape.Embedding.BoundaryGE, not_and, not_forall, not_not] at hj
    obtain ⟨i, hi⟩ := hj hj'
    rw [e.rel_iff] at hi
    rw [c.prev_eq' hi] at hij
    exact hij' (by simpa only [hij] using hi)

