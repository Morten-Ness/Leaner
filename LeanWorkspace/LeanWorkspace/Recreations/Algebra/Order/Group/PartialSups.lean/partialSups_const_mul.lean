import Mathlib

variable {α ι : Type*}

variable [SemilatticeSup α] [Group α] [Preorder ι] [LocallyFiniteOrderBot ι]

theorem partialSups_const_mul [MulLeftMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (c * f ·) i = c * partialSups f i := map_partialSups (OrderIso.mulLeft _) ..

