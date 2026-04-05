import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_op (op : ∀ i, M i → N i) (h : ∀ i, op i 1 = 1) (i : ι) (x : M i) :
    Pi.mulSingle i (op i x) = fun j => op j (Pi.mulSingle i x j) := .symm <| funext <| Pi.apply_mulSingle op h i x

