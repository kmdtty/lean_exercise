universe u
variables {A B : Sort*}

def areIso (X Y: Type u) : Prop :=
  ∃ f : X → Y, ∃ g : Y → X, f ∘ g = @id Y ∧ g ∘ f = @id X
