import Mathlib

variable {ι : Type*}

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

theorem GradedMonoid.list_prod_ofFn_eq_dProd {n : ℕ} (f : Fin n → GradedMonoid A) :
    (List.ofFn f).prod =
      GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [List.ofFn_eq_map, GradedMonoid.list_prod_map_eq_dProd]

