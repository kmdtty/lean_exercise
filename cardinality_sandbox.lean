import set_theory.cardinal

-- import init.classical
open cardinal

#eval if 2 < 7 then 1 else 0 


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
-- noncomputable theory 


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

-- Define powerset
variable {U : Type}


example (A B : set U) (h : B ∈ powerset2 A) : B ⊆ A :=
h
def y2 : set ℕ := {1,2}
variable {y : set ℕ}
#check set ℕ
#reduce (set ℕ) 
#print y
#print set
#reduce 2 ∈ y
#reduce 2 ∈ y2
#reduce y2 19
#print y2
#check y2
#print ∈
#print has_mem
#check Prop
#reduce Prop
#print Prop
#check y → Prop
#reduce y → Prop
#reduce y2 → Prop

#check list -- list: Type u_3 → Type u_3
#check vector -- vector: Type u_3 → ℕ → Type_u_3
#print vector 
-- @[_ext_core id.{1} name vector.ext] 
--def vector : Type u → ℕ → Type u :=
--λ (α : Type u) (n : ℕ), {l // l.length = n}

#print list 
--
--@[_ext_core id.{1} name list.ext]
--inductive list : Type u → Type u
--constructors:
--list.nil : Π {T : Type u}, list T
--list.cons : Π {T : Type u}, T → list T → list T

#print set 
--@[_ext_core id.{1} name set.ext]
--def set : Type u → Type u :=
--λ (α : Type u), α → Prop

universe u 
#check Type u -- Type (u+1) -- !! not Type u
#check Type -- Type 1
#check Prop -- Type 

def v' := λ f: ℕ → ℕ, f 1

#check v'  -- v' : (ℕ → ℕ) → ℕ
#print v' -- def v' : (ℕ → ℕ) → ℕ := λ (f : ℕ → ℕ), f 1

def double' : ℕ → ℕ := λ x: ℕ , x+ x
def double'' (x: ℕ) : ℕ := x + x

-- double' and double'' are equivalent
#check double' -- double' : ℕ → ℕ
#check double'' -- double'' : ℕ → ℕ
#print double'  -- def double' : ℕ → ℕ := λ (x : ℕ), x + x
#print double'' --  def double'' : ℕ → ℕ := λ (x : ℕ), x + x

