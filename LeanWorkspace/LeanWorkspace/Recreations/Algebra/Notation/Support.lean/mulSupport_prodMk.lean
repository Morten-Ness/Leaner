import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_prodMk (f : ι → M) (g : ι → N) :
    Function.mulSupport (fun x ↦ (f x, g x)) = Function.mulSupport f ∪ Function.mulSupport g := Set.ext fun x ↦ by
    simp only [Function.mulSupport, not_and_or, mem_union, mem_setOf_eq, Prod.mk_eq_one, Ne]

