import Mathlib

section

variable {I : Type u}

variable {f : I → Type v}

theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single (M := fun _ => β) i (r • x) = r • single (M := fun _ => β) i x :=
  Pi.single_smul (f := fun _ => β) i r x

end

section

variable {I : Type u}

variable {f : I → Type v}

theorem single_smul {α} [Monoid α] [∀ i, AddMonoid <| f i] [∀ i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x := single_op (fun i : I => (r • · : f i → f i)) (fun _ => smul_zero _) _ _

end

section

variable {I : Type u}

variable {f : I → Type v}

theorem single_smul₀ {g : I → Type*} [∀ i, MonoidWithZero (f i)] [∀ i, AddMonoid (g i)]
    [∀ i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x := single_op₂ (fun i : I => ((· • ·) : f i → g i → g i)) (fun _ => smul_zero _) _ _ _

end
