import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : ι → M) (g : ι → N) :
    Function.mulSupport (fun x ↦ op (f x) (g x)) ⊆ Function.mulSupport f ∪ Function.mulSupport g := fun x hx ↦
  not_or_of_imp fun hf hg ↦ hx <| by simp only [hf, hg, op1]

