import Mathlib

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

theorem tensorProdIsoPushout_app (A : Under R) :
    (CommRingCat.tensorProdIsoPushout R S).app A = CommRingCat.tensorProdObjIsoPushoutObj S A := rfl

