import Mathlib

variable {ι : Type*}

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

theorem List.dProdIndex_eq_map_sum (l : List α) (fι : α → ι) :
    l.dProdIndex fι = (l.map fι).sum := by
  match l with
  | [] => simp
  | head::tail => simp [List.dProdIndex_eq_map_sum tail fι]

