import data.set 
import data.nat.basic
import set_theory.cardinal

open set 
open cardinal

#check [1,2] 

universe u
--variables {A B : Sort*}
-- What's the diffrence between `Type` and `Type u` ?
variables {α β : Type u}
-- A, B are subsets of α
-- A ⊂ α ↔ A ∈ 𝒫(A)
variables {A B C: set α}
variables {a b c : Type u}
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
noncomputable theory 
open_locale cardinal
#check cardinal.mk α
#check #α^#β -- `#α` is the notation of `cardinal.mk α` in set_theory/cardinal

#check 2

-- #check #α^#β
theorem powerset_equinumerous_set_of_function
 {f: A → bool} : powerset(A) ∼ set f :=
  sorry

#eval if 2 < 7 then 1 else 0 

-- to solve type error on "if .. then ..else.." we need the following two lines
-- `noncomuptable theory` is alread defined above to open_local cardinal
open_locale classical 

--- wrong definition? 
/-- `indicator' s x` is `1` if `x ∈ s`, `0` otherwise. -/
--def indicator' (s : set α) (x : α) : ℕ := if x ∈ s then 1 else 0


-- The notation of power `^` is defined in set_theory/cardinal.lean

--  instance : has_pow cardinal cardinal := ⟨cardinal.power⟩
--  local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow

-- Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
-- in src/set_theory/cardinal.lean
-- https://leanprover-community.github.io/mathlib_docs/set_theory/cardinal.html

/-- The cardinal exponential. `mk α ^ mk β` is the cardinal of `β → α`. -/ 


-- @[simp] theorem power_def (α β) : mk α ^ mk β = mk (β → α) := rfl                             

-- from data/set/basic.lean
variable {ι : Type*} 
variable {α' : ι → Type*}
variables {s s₁ : set ι}
variables {t t₁ t₂ : Π i, set (α' i)}

/-- The cartesian product `prod s t` is the set of
 `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def prod' (s : set α) (t : set β) : 
set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

/-- Given an index set `ι` and a family of sets
  `t : Π i, set (α i)`, `pi s t`
  is the set of dependent functions
   `f : Πa, π a` such that `f a` belongs to `t a`
  whenever `a ∈ s`. -/
def pi (s : set ι) (t : Π i, set (α' i)) :
 set (Π i, α' i) := { f | ∀i ∈ s, f i ∈ t i }


@[simp] lemma mem_pi {f : Π i, α' i} : 
f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=         
by refl   

#check α'

#check prod' A B 
#check prod' {α} {β}
#reduce prod' A B
#reduce prod' {α} {β}
#check (set α)

#eval 1 + 2
--#check set({a b})
#reduce (a, b).1
#reduce (a, b).2
#check [1, 2] -- list ℕ 
#check [a,b] -- List (Type u)
--instance i: (x: nat) (y: nat) := ⟨1, 2⟩
def v : set nat := {1,2}
#check v 

def v2 : set nat := {2, 3}

#reduce 2 ∈ v
#check 2 ∈ v





