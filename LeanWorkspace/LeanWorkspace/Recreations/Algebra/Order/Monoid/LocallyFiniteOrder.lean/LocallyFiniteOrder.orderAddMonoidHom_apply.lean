import Mathlib

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

theorem LocallyFiniteOrder.orderAddMonoidHom_apply (x : G) :
    orderAddMonoidHom G x = addMonoidHom G x := rfl

