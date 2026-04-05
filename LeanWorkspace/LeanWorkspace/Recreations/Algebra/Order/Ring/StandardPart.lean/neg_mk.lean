import Mathlib

theorem neg_mk {x : K} (h : 0 ≤ ArchimedeanClass.FiniteElement.mk x) :
    -ArchimedeanClass.FiniteElement.mk x h = ArchimedeanClass.FiniteElement.mk (-x) (by rwa [mk_neg]) := rfl

