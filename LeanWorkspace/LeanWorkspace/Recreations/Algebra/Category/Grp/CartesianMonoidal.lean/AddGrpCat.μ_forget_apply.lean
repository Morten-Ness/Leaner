import Mathlib

theorem μ_forget_apply {G H : AddGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddGrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddGrpCat.{u}) G H) (p, q)

