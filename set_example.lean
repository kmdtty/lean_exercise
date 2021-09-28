import data.set 
import data.set.basic
import set_theory.zfc 
-- import data.nat.basic
-- import set_theory.cardinal

-- open Set 

open set 
--open cardinal

universes u v
variables {α β : Type u}
variables {a b c: Type u}
variables {A C: set α}
variable B: set β

#check prod α β
#reduce prod A B
#check α
#check (set α)

#eval 1 + 2
--#check set({a b})
#check (a,b)
#reduce (a, b).1
#reduce (a, b).2
#check [1, 2] -- list ℕ 
#check [a,b] -- List (Type u)
--instance i: (x: nat) (y: nat) := ⟨1, 2⟩
def v : set nat := {1,2}
#check v 

def v2 : set nat := {2, 3}

def v3: set (ℕ × ℕ)  := {(1,2), (2,4)}
def v4: set(ℕ × ℕ) := {(1,2),(3,4)}

def powerset' (A : set α) : set (set α) := {B : set α | B ⊆ A}

#reduce ∃⦃x:v3⦄, x.val.1 = 1 ∧ x.val.2 = 4
#print v3
#reduce (1,2) ∈ v3
#print powerset
#reduce powerset A
#reduce v × v2
-- #reduce (1,2) ∈ set(v × v2)
#reduce 1 ∈ v2
#reduce 2 ∈ v
#reduce 1 ∈ v
#reduce A × B
#reduce powerset A × B  -- this is parsed with: powerset (A) × B
#reduce powerset v2 × v2 -- parswed with: powerset (v2) × v2
#reduce powerset' {v2 × v2} --set(v2 × v2)
#check v2 × v2
#print ×
#print prod 
#check prod v2 v2
#check set (prod v2 v2)
#reduce (2,2) ∈  {v2 × v2} 
--#check (2,2) ∈ set (v2 × v2)
#check A × B 
#check set (A × B)
#check powerset {A × B}
#check powerset A
#reduce powerset A 
#reduce powerset {A × B}
#check powerset {A × B}
#check (1,2) ∈ powerset {A × B}
#check powerset {v2 × v2} 
#check (2,2) ∈ powerset {v2 × v2}
#reduce (2,2) ∈ powerset {v2 × v2}
#check set (powerset {v2 × v2})
#check ℕ × ℕ 
#check set (ℕ × ℕ)
-- are these same?
def p : ℕ × ℤ := ⟨ 1, 2 ⟩ 
def p2 : ℕ × ℤ := (1, 2)
#check p
#check p2

#check Π x : α, β
#check λ x: α, β

-- these are same
#check fun x: nat, x + 5
#check λ x: nat, x+ 5

#print ∣ 
def evens : set ℕ := {n | even n}
#check nat × nat
#check evens
variable n':nat
def n₂ : ℕ := 10
#check even n₂ 
#reduce even n₂ 

--variable e:nat 
variable s': set ℕ
#check 1 ∈ s'
-- caution!! `∣`(\mid) and `|` is different!! we can not use \mid in 
-- set comprehension.
def test_false : set ℕ := {e | even e }
#check test_false
variables {A' B': set ℕ}
#check A' × B'
#check powerset {A' × B'}
#check {(a,b)} ∈ powerset {A × B}
#print A 
#print powerset
-- This does not raises error but `set (set Type u)` does not seem what we want
def test_function_from_set : set (set(Type u)) := {f | f ⊆ {A × B}}
--def test_function_from_set : set (set(A × B)) := 
-- {sf | sf ∈ powerset (A.prod B)}
def test_function_from_set2 {X' X'': set ℕ}: set (set(ℕ × ℕ)) :=
 {sf | sf ∈ powerset (X'.prod X'')}

namespace test
variables X Y: set ℕ 
#check X × Y
variables x: ℕ  × ℕ 
#check x
-- !caution! `prod X Y` and `set.prod X Y` are different!! 
#check prod X Y -- ↥X × ↥Y : Type
#check set.prod X Y -- set (ℕ × ℕ) : Type ;; is equivalent to `X.prod Y`
#check set (prod X Y)
#print set.prod -- {p : α × β | p.fst ∈ s ∧ p.snd ∈ t}
#print prod
#print × -- prod 

def t {X Y: set ℕ}: set(ℕ × ℕ) := X.prod Y 
def t' : set(ℕ × ℕ) := X.prod Y 

#check t -- t : set (ℕ × ℕ)
#check t' -- t' : set ℕ → set ℕ → set (ℕ × ℕ)
#check t' 3 5 -- t' 3 5 : set (ℕ × ℕ)  ; t' requires two parameters!
#check x ∈ t

variable f₂: ℕ → ℕ  
#check f₂

variable f₃: α → β
#check f₃
#check ℕ 

namespace function
def graph {α β: Type u} (f: α → β) : set (α × β) := {p | p.2 = f p.1}
end function
#check function.graph(f₃)

def test_function_from_set2 {X' X'': set ℕ}: set (set(ℕ × ℕ)) :=
 {sf | sf ∈ powerset (X'.prod X'')}

variables {D E: set (Type u)}
#check {p | p ∈ 𝒫(D.prod E)}
-- not yet defined

def setA {a: α} : set α:= {a | a ∈ A} 
def setA2 {A2: set α}: set α := {a | a ∈ A2}
def setN {N: set ℕ}: set ℕ := {n | n ∈ N}
variable θ: Type
def setC {C2: set θ} :set θ := {c | c ∈ C2}

-- Type*, Type u, Type _ is used for dependant type
variable γ : Type* -- to avoid arbitaly universe name we can use `Type*`
#check α -- Type u
#check γ -- Type u_1
#check setN -- set ℕ 
#check setA -- set ?M_1 (this can not have set `α` because `α` is `Type u`)
#check setA2 -- set ?M_1
#check setC -- set θ (this have type `set θ` is because `θ` is `Type`)
#check ℕ -- Type
#print ℕ -- `ℕ`:1024 := nat
#check A -- set α
#check {l | l ∈ setA} -- set ?M_1
#check {l2 | l2 ∈ A} -- set α
-- We can not remove the hint `{setA: set α}` from `setA_from_setA` definition.
-- Is this because `def` has its own scope that `setA` is missing the type info?
def setA_from_setA {setA: set α}: set α := {x | x ∈ setA}
-- Why OK? because the scope inside the {} is global?
#check {l: α | l ∈ setA}
end test
--#reduce {f:nat × nat ∣ f ∈ powerset {v2 × v2}}don't know how to synthesize placeholder
-- #check {n sf ∣ n ∈ ℕ}
--#reduce {f ∣ f ∈ powerset {v2 × v2}}
-- v = {1,2}, v2 = {2,3}
-- v × v2 = {(1,2),(1,3),(2,2),(2,3)}
-- powerset v × v2 = {∅,
--                    {(1,2)}, {(1,2),(1,3)},{(1,2),(2,2)},{(1,2),(2,3)},{}
--                    {(1,3),(2,2)}, {(1,3),(2,3)},
--                    {(2,2),(2,3)},
--                    {(1,2),(1,3),(2,2)},{(1,2),(2,2),(2,3)},
--                    {(1,3),(2,2),(2,3)},
--                    {(1,2),(1,3),(2,2),(2,3)}}

namespace test2
#check a
#check α
#check 'a'
-- We can not define the following
-- def onetwo : α×β := ⟨α, β⟩   
def ab : char × char := ⟨ 'a', 'b'⟩ 
#print char
#print nat 
#print α 
#check (1,2) 
def sf₁ : set (set (ℕ × ℕ)) := {{(1,2)},{(1,2),(1,3)}}
-- def sf₂ : set (set (α × β)) := {{⟨a,b⟩ },{(a,b)}}
#check sf₁

def npair : ℕ × ℕ := (1,2)
#check npair -- npair : ℕ × ℕ

def npair₂ : ℕ × ℕ := ⟨1,2⟩  -- whats the difference on `()` and `⟨ ⟩`?
#check npair₂ -- npair₂ : ℕ × ℕ 

def nset₁ : set ℕ := {1,2}
def nset₂ : set ℕ := {1,2}

-- we can not call this. why?
--#check nset₁.prod nset₂
#check nset₁ -- set: ℕ 
-- we can not infer the type of {1,2}
--def setnpair : set (ℕ × ℕ) := {1,2}.prod {2,3}
-- the type is `set (ℕ × ℕ)` (not `(set ℕ) × (set ℕ)`) 
def npairset : set (ℕ × ℕ) := ({1,2}:set ℕ).prod ({2,3}:set ℕ)  
#check npairset -- set (ℕ × ℕ)
#reduce npairset

def npairset₂ : set (ℕ × ℕ) := {(1,2),(3,4),(5,6)}

#check npairset₂ -- npaierset₂ : set (ℕ × ℕ )
#reduce npairset₂ -- λ (b : ℕ × ℕ), b = (1, 2) ∨ b = (3, 4) ∨ b = (5, 6)

def setnpair : set ℕ × set ℕ := ⟨ {1,2,3} , {2,3,4,5} ⟩ 
#check setnpair -- set ℕ × set ℕ 
#check A -- set α
#check A.prod B -- set (α × β)

-- When the type is ℕ
variables {n₁ n₂ : ℕ}
variable {N₁: set ℕ}
variable {N₂: set ℕ}
#check N₁.prod N₂ -- set (ℕ × ℕ) 
#check (1,2) ∈ N₁.prod N₂ --(X.prod Y)
#check (n₁,n₂) ∈ N₁.prod N₂

#print ℕ
#print nat

-- When it is generic Type
variables {x₁ y₁: Type}
variables {X₁: set Type}
variables {Y₁: set Type}
#check X₁.prod Y₁ -- X₁.prod Y₁ : set (Type × Type)
#check (x₁,y₁) ∈ X₁.prod Y₁

variable f₁ : set (Type × Type)
#check f₁ -- f₁ : set (Type × Type)
#check set(X₁ × Y₁)  -- set (↥X₁ × ↥Y₁) : Type 1
#check ↥X₁
#reduce ↥X₁ -- {x // X₁ x}
#check ↥X₁ × ↥Y₁ -- ↥X₁ × ↥Y₁ : Type 1
#reduce coe_sort X₁
#check X₁.prod Y₁ -- X₁.prod Y₁ : set (Type × Type)
#check (x₁,y₁) -- (x₁, y₁) : Type × Type
#check (x₁,y₁) ∈ f₁ -- (x₁, y₁) ∈ f₁ : Prop
#check coe_sort X₁ × coe_sort Y₁ -- ↥X₁ × ↥Y₁ : Type 1
#check coe_sort X₁
--#check (x₁, y₁) ∈ (X₁ × Y₁)
#check ↑X₁ --↑X₁ : ?M_1
#check subtype X₁ -- subtype X₁ : Type 1

variable s : set α
#check subtype s 

/-- invalid definition -/
-- Pitfalls
-- ========
-- 1. f is not `set (X × Y)` because `X` is `set Type*`, it means it is a term
---   not a type, so `X × Y` does not work as expected.
-- 2. `x:X` is expected to express `x ∈ X`, but again
--    `X` is not an expected type. (it is coerced type ↥X in reality)  
--    Thus `x:X` does not mean `x` is a member of the set `X`.
--    It does not mean `x` is a type of `Type*`. Instead,
--    it means `x` has a type of `↥X`, then `(x, y)` has a type `(↥X, ↥Y)`.
def is_function_invalid (X Y: set Type*) (f: set (X × Y)): Prop := 
 ∀x:X,∃!y:Y, (x,y) ∈ f

/-- invalid definition -/
def funs_invalid {X Y: set Type*} : set (set (X × Y)) :=
{f | f ∈ 𝒫 (X.prod Y) ∧ (is_function_invalid X Y f)}

/--
The function x is a triple: (T, T, (T, T)) (T can be any type)   
-/
def is_function (X:set α) (Y: set β) (f: set (α × β)): Prop := 
 ∀x ∈ X,∃!y ∈ Y, (x,y) ∈ f

-- not yet defined
-- `funs X Y` is `Y ^ X`
def funs (X : set α) (Y: set β): set (set (α × β)) :=
{f | f ∈ 𝒫 (X.prod Y) ∧ (is_function X Y f)}

theorem mem_funs_eq_isfunction {X: set α} {Y: set β } {f: set (α × β)}: 
f ∈ funs X Y ↔ is_function X Y f :=
by simp [funs, is_function]



--variable a_number₂ : 
--def setN: set ℕ := {n | n: ℕ}
def example2 {n: ℕ} : Prop := n = 1
--lemma example3: ∀n:ℕ, n = 1 := sorry
#print set

-- universes u v
-- this definition is from library/init/data/set.lean
def set₁ (α : Type u) := α → Prop


end test2

namespace ZFCSet

-- These definitions are copied from set_theorey/zfc.lean

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
inductive pSet : Type (u+1)
| mk (α : Type u) (A : α → pSet) : pSet

#check pSet

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
def Set : Type (u+1) := quotient pSet.setoid.{u}

#check Set
#reduce Set.{u}
#check Set.{v}
#print pSet.setoid

--variable (x : Set.{u})

notation `⋃` := Set.Union

/-- Kuratowski ordered pair -/
def pair (x y : Set.{u}) : Set.{u} := {{x}, {x, y}}

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pair_sep (p : Set.{u} → Set.{u} → Prop) (x y : Set.{u}) : Set.{u} :=
{z ∈ powerset (powerset (x ∪ y)) | ∃a ∈ x, ∃b ∈ y, z = pair a b ∧ p a b}

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : Set.{u} → Set.{u} → Set.{u} := pair_sep (λa b, true)

/-- `is_func x y f` is the assertion `f : x → y` where `f` is a ZFC function
  (a set of ordered pairs) -/
def is_func (x y f : Set.{u}) : Prop :=
f ⊆ prod x y ∧ ∀z:Set.{u}, z ∈ x → ∃! w, pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : Set.{u}) : Set.{u} :=
{f ∈ powerset (prod x y) | is_func x y f}

end ZFCSet