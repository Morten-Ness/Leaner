import Mathlib

theorem μ_forget_apply {G H : AddCommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddCommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddCommGrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddCommGrpCat.{u}) G H) (p, q)

