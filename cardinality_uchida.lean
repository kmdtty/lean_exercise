import data.set 
import data.nat.basic
import data.rel 

open set 

universe u
variables {α β : Type u}
variables {A B C: set α}
variables {a b c : Type u}


/--
Let X Y be a set,
f be a pairs of X × Y.
The function x is a triple: x := (f, X, Y)    

Note that:
`∀x ∈ X` means `∀x: α, x ∈ X → ...`  
`∃y ∈ Y` means `∃y: β, y ∈ Y ∧ ... `

We can not eliminate `f ⊆ X.prod Y` form `is_function` defintion,
it means `f` is a relation beteen `X` and `Y`, but I am not sure why it is needed.
-/
def is_function  (f: set (α × β)) (X:set α) (Y: set β): Prop := 
f ⊆ X.prod Y ∧ ∀x ∈ X,∃!y ∈ Y, (x,y) ∈ f

/--
`funs X Y` is the set of all functions `f: X → B`

`funs X Y` is denoted `Y ^ X`.
-/
def funs (X : set α) (Y: set β): set (set (α × β)) :=
{f | f ∈ 𝒫 (X.prod Y) ∧ (is_function f X Y)}

#print 𝒫 -- `𝒫`:100 _:100 := set.powerset #0
#print set.powerset 
-- def set.powerset : Π {α : Type u}, set α → set (set α) :=
--  λ {α : Type u} (s : set α), {t : set α | t ⊆ s}

-- This prove `by simp [funs, is_function]` is copied from set_theory/zfc.lean 
-- I have not yet understood this proof.
theorem mem_funs_equiv_isfunction {X: set α} {Y: set β } {f: set (α × β)}: 
f ∈ funs X Y ↔ is_function f X Y :=
by simp [funs, is_function]

variable X : set α
variable Y: set β

#check rel X Y
#print rel

/--
§7. Cardinality
-/

-- Exercise 7.1 

-- are_equinumeros?
def are_iso (X Y: set α) : Prop :=
  ∃ f : X → Y, ∃ g : Y → X, f ∘ g = @id Y ∧ g ∘ f = @id X

#check are_iso A B

local infixr ` ∼ `:max := are_iso 

-- ex 7.1 (1)
theorem iso_reflexivity :  A ∼ A :=
  sorry  

-- ex 7.1 (2)
theorem iso_symmetry : A ∼ B → B ∼ A :=
  sorry

-- ex 7.1 (3)
theorem iso_transivity : A ∼ B ∧ B ∼ C → A ∼ C :=
  sorry

theorem powerset_equinumerous_set_of_function
 {f: A → bool} : powerset(A) ∼ set f :=
  sorry
