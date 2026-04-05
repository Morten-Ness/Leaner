import Mathlib

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

theorem LocallyFiniteOrder.orderMonoidHom_strictMono {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    StrictMono (orderMonoidHom G) := let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  fun a b h ↦ orderAddMonoidHom_strictMono h

