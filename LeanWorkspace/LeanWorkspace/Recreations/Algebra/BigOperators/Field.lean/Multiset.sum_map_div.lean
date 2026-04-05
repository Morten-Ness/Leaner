import Mathlib

variable {ι K : Type*} [DivisionSemiring K]

theorem Multiset.sum_map_div (s : Multiset ι) (f : ι → K) (a : K) :
    (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

