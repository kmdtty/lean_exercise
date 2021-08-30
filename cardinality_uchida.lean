import data.set 
import data.nat.basic
open set 

#check [1,2] 

universe u
--variables {A B : Sort*}
-- What's the diffrence between `Type` and `Type u` ?
variables {α: Type u}
-- A, B are subsets of α
-- A ⊂ α ↔ A ∈ 𝒫(A)
variables {A B C: set α}
#check set α
#check α
#check set

-- are_equinumeros?
def are_iso (X Y: set α) : Prop :=
  ∃ f : X → Y, ∃ g : Y → X, f ∘ g = @id Y ∧ g ∘ f = @id X

#check are_iso A B
#check powerset


-- Define powerset
variable {U : Type}

def powerset2 (A : set U) : set (set U) := {B : set U | B ⊆ A}

example (A B : set U) (h : B ∈ powerset2 A) : B ⊆ A :=
h

local infixr ` ∼ `:max := are_iso 

theorem iso_reflexivity :  A ∼ A :=
  sorry  

theorem iso_symmetry : A ∼ B → B ∼ A :=
  sorry

theorem iso_transivity : A ∼ B ∧ B ∼ C → A ∼ C :=
  sorry

-- variables 0 1 : ℕ 
/--
inductive nat
| zero : nat
| succ (n : nat) : nat

inductive bool : Type
| ff : bool
| tt : bool
-/
-- the syntax of the following definition is wrong on {0 1} (at least)
theorem powerset_equinumerous_set_of_function {f: A → bool } : powerset(A) ∼ set f :=
  sorry