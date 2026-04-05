import Mathlib

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

theorem LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono {G : Type*}
    [LinearOrderedCommGroupWithZero G] [LocallyFiniteOrder Gˣ] :
    StrictMono (orderMonoidWithZeroHom G) := by
  have := orderMonoidHom_strictMono (G := Gˣ)
  intro a b h
  aesop (add simp orderMonoidWithZeroHom)

