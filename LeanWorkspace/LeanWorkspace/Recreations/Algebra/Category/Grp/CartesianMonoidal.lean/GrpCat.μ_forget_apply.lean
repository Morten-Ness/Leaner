import Mathlib

theorem μ_forget_apply {G H : GrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget GrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget GrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget GrpCat.{u}) G H) (p, q)

