import data.set 
import data.nat.basic
import data.set.function
import data.rel 

open set 
open function

universe u
variables {α β : Type*}
variables {A B C: set α}
variable D : set β
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
`Functions X Y` is the set of all functions `f: X → B`

`Functions X Y` is denoted `Y ^ X`.
-/
def Functions (X : set α) (Y: set β): set (set (α × β)) :=
{f | f ∈ 𝒫 (X.prod Y) ∧ (is_function f X Y)}

--
local notation b `^`:100 a := Functions a b

#print 𝒫 -- `𝒫`:100 _:100 := set.powerset #0
#print set.powerset 
-- def set.powerset : Π {α : Type u}, set α → set (set α) :=
--  λ {α : Type u} (s : set α), {t : set α | t ⊆ s}

-- This prove `by simp [funs, is_function]` is copied from set_theory/zfc.lean 
-- I have not yet understood this proof.
theorem mem_funs_equiv_isfunction {X: set α} {Y: set β } {f: set (α × β)}: 
f ∈ Functions X Y ↔ is_function f X Y :=
by simp [Functions, is_function]

variable X : set α
variable Y: set β

#check rel X Y
#print rel

/--
§7. Cardinality
-/

-- Exercise 7.1 

def are_iso (X:set α) (Y: set β) : Prop :=
  ∃ f : X → Y, ∃ g : Y → X, f ∘ g = @id Y ∧ g ∘ f = @id X

def are_equinumero (X:set α) (Y: set β) : Prop :=
  ∃ f : X → Y, bijective f

-- not yet proved 
theorem are_iso_eq_are_equinumero {X: set α} {Y: set β}:
(are_iso X Y) ↔ (are_equinumero X Y) :=
by simp [are_iso, are_equinumero]

#check X → Y -- ↥X → ↥Y : Type (max u_1 u_2)

#check are_iso A B

local infix ` ∼ `:max := are_iso 
-- local notation a `∼` b := are_iso a b

-- ex 7.1 (1)
theorem iso_reflexivity :  A ∼ A :=
  sorry  

-- ex 7.1 (2)
theorem iso_symmetry : A ∼ B → B ∼ A :=
  sorry

-- ex 7.1 (3)
theorem iso_transivity : A ∼ B ∧ B ∼ C → A ∼ C :=
  sorry

--def 𝔹 : set ℕ := {0,1}

inductive 𝔹 : Type
| zero : 𝔹
| one : 𝔹

def 𝔹₂: set 𝔹 := {𝔹.zero, 𝔹.one}

#check A -- A : set α
#check Functions A B 
#check 𝔹₂ -- 𝔹₂ : set 𝔹
 
#check Functions A 𝔹₂
#check 𝔹₂ ^ A -- 𝔹₂ ^ A : set (set (α × 𝔹))
#check 𝒫(A) -- 𝒫 A : set (set α)
#check α × 𝔹 -- α × 𝔹 : Type u_1
#reduce α × 𝔹 
#check α -- α : Type u_1
def B₂A: set (set (α × 𝔹)) := 𝔹₂ ^ A

#check are_iso 𝒫(A) 𝒫(B) -- (𝒫 A) ∼ 𝒫 B : Prop
#check (𝒫 A) ∼ (𝒫 B) 
#check are_iso (𝒫 A) (𝔹₂ ^ A)

#check (𝒫 A) ∼ (𝔹₂ ^ A) -- 𝒫 A ~ 𝔹₂ ^ A : Prop
#reduce (𝒫 A) ∼ (𝔹₂ ^ A)
#reduce are_iso (𝒫 A) (𝔹₂ ^ A)

theorem powerset_A_equiv_powerset_A:
(𝒫 A) = (𝒫 A) :=
by refl 

theorem powerset_A_equinumerous_set_of_function_from_A_to_bool : 
(𝒫 A) ∼ (𝔹₂ ^ A) := sorry