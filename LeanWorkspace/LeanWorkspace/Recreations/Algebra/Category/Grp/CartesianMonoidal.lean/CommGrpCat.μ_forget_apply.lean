import Mathlib

theorem μ_forget_apply {G H : CommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget CommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget CommGrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget CommGrpCat.{u}) G H) (p, q)

