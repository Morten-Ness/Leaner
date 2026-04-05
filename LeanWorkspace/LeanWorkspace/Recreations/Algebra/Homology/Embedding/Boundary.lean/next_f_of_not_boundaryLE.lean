import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem next_f_of_not_boundaryLE [e.IsRelIff] {j k : ι} (hjk : c.next j = k)
    (hj : ¬ e.BoundaryLE j) :
    c'.next (e.f j) = e.f k := by
  by_cases hjk' : c.Rel j k
  · exact c'.next_eq' (by simpa only [e.rel_iff] using hjk')
  · obtain rfl : j = k := by
      simpa only [c.next_eq_self j (by simpa only [hjk] using hjk')] using hjk
    apply c'.next_eq_self
    intro hj'
    simp only [ComplexShape.Embedding.BoundaryLE, not_and, not_forall, not_not] at hj
    obtain ⟨k, hk⟩ := hj hj'
    rw [e.rel_iff] at hk
    rw [c.next_eq' hk] at hjk
    exact hjk' (by simpa only [hjk] using hk)

