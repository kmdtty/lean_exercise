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

#check A → Prop 
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

theorem powerset_equinumerous_set_of_function {f: A → Prop } : powerset(A) ∼ set f :=
  sorry

#eval if 2 < 7 then 1 else 0 

-- from src/algebra/indicator_function.lean
-- to solve type error on "if .. then ..else.." we need the following two lines
noncomputable theory 
open_locale classical 
/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/     
def indicator {M} [has_zero M] (s : set α) (f : α → M) : α → M := λ x, if x ∈ s then f x else 0

#check indicator
--- wrong definition? 
/-- `indicator2 s x` is `1` if `x ∈ s`, `0` otherwise. -/
def indicator2 (s : set α) (x : α) : ℕ := if x ∈ s then 1 else 0

