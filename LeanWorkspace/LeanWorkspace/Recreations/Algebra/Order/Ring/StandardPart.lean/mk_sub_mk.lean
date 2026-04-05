import Mathlib

theorem mk_sub_mk (x y : K) (hx hy) :
    .mk x hx - .mk y hy = ArchimedeanClass.FiniteElement.mk (x - y) ((le_min hx hy).trans <| min_le_mk_sub ..) := rfl

