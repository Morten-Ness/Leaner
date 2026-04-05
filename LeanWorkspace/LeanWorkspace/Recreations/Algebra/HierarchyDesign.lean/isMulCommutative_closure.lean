import Mathlib

theorem isMulCommutative_closure {G : Type*} [Group G] {k : Set G}
    (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    IsMulCommutative (closure k)
```
or even *instances* such as
```
