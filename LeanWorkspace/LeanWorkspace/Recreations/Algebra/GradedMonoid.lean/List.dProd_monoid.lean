import Mathlib

variable {ι : Type*}

variable (ι) {R : Type*}

theorem List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α → ι) (fA : α → R) :
    @List.dProd _ _ (fun _ : ι => R) _ _ l fι fA = (l.map fA).prod := by
  match l with
  | [] =>
    rw [List.dProd_nil, List.map_nil, List.prod_nil]
    rfl
  | head::tail =>
    rw [List.dProd_cons, List.map_cons, List.prod_cons, List.dProd_monoid tail _ _]
    rfl

