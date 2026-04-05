import Mathlib

variable {ι : Type*}

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

theorem GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α → GradedMonoid A) :
    (l.map f).prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [GradedMonoid.mk_list_dProd, GradedMonoid.mk]
  simp_rw [Sigma.eta]

