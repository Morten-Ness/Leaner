import Mathlib

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

theorem LocallyFiniteOrder.orderAddMonoidHom_strictMono :
    StrictMono (orderAddMonoidHom G) := by
  rw [strictMono_iff_map_pos]
  intro g H
  simpa [addMonoidHom, H.le]

