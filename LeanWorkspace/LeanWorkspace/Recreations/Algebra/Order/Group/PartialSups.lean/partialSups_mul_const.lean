import Mathlib

variable {α ι : Type*}

variable [SemilatticeSup α] [Group α] [Preorder ι] [LocallyFiniteOrderBot ι]

theorem partialSups_mul_const [MulRightMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (f · * c) i = partialSups f i * c := map_partialSups (OrderIso.mulRight _) ..

