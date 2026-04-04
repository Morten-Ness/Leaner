import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable (k V)

variable {V}

variable {k}

theorem AffineIndependent.affineIndependent_update_of_notMem_affineSpan [DecidableEq ι]
    {p : ι → P} (ha : AffineIndependent k p) {i : ι} {p₀ : P}
    (hp₀ : p₀ ∉ affineSpan k (p '' {x | x ≠ i})) :
    AffineIndependent k (Function.update p i p₀) := by
  set f : ι → P := Function.update p i p₀ with hf
  have h₁ : (fun x : {x | x ≠ i} ↦ p x) = fun x : {x | x ≠ i} ↦ f x := by ext x; aesop
  have h₂ : p '' {x | x ≠ i} = f '' {x | x ≠ i} := Set.image_congr <| by simpa using congr_fun h₁
  replace ha : AffineIndependent k fun x : {x | x ≠ i} ↦ f x := h₁ ▸ AffineIndependent.subtype ha _
  exact AffineIndependent.affineIndependent_of_notMem_span ha <| by aesop

