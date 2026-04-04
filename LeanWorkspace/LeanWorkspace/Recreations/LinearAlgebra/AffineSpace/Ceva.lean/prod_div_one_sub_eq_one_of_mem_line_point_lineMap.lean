import Mathlib

variable {k V P ι : Type*}

variable [Field k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem prod_div_one_sub_eq_one_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 → k}
    (hr0 : ∀ i, r i ≠ 0) {p' : P} (hp' : ∀ i : Fin 3, p' ∈
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i / (1 - r i) = 1 := by
  rw [Finset.prod_div_distrib, ← Affine.Triangle.prod_eq_prod_one_sub_of_mem_line_point_lineMap hp', div_self]
  exact Finset.prod_ne_zero_iff.2 fun _ _ ↦ hr0 _

