import Mathlib

theorem CommGroup.ext {G : Type*} ⦃g₁ g₂ : CommGroup G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul

