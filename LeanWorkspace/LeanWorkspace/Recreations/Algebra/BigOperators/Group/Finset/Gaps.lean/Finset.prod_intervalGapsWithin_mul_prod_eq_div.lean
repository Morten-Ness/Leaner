import Mathlib

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (F : Finset (α × α)) {k : ℕ} (h : F.card = k) {a b : α}
  (g : α → β)

theorem Finset.prod_intervalGapsWithin_mul_prod_eq_div :
    (∏ i ∈ Finset.range (k + 1),
      g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) *
      ∏ z ∈ F, g z.2 / g z.1 = g b / g a := by
  rw [F.prod_eq_prod_range_intervalGapsWithin h (fun x y ↦ g y / g x), mul_comm,
      prod_range_succ, ← mul_assoc,
      ← prod_mul_distrib,
      prod_congr rfl (fun _ _ ↦ div_mul_div_cancel _ _ _),
      prod_range_div (fun i ↦ g (F.intervalGapsWithin h a b i).1)]
  simp

