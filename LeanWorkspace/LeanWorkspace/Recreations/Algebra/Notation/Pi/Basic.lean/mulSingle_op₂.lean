import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_op₂ (op : ∀ i, M i → N i → O i) (h : ∀ i, op i 1 1 = 1) (i : ι) (x : M i)
    (y : N i) : Pi.mulSingle i (op i x y) = fun j ↦ op j (Pi.mulSingle i x j) (Pi.mulSingle i y j) := .symm <| funext <| Pi.apply_mulSingle₂ op h i x y

