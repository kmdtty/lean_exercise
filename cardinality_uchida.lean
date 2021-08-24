import data.set 
open set 

universe u
variables {A B : Sort*}
variables {α: Type u}
#check set α
#check α
#check set

def areIso (X Y: Type u) : Prop :=
  ∃ f : X → Y, ∃ g : Y → X, f ∘ g = @id Y ∧ g ∘ f = @id X

