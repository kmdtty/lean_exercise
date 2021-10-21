import set_theory.cardinal

-- import init.classical

variable α : Type*
variable β : Type*

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
-- open_locale classical 

--- wrong definition? 
/- `indicator' s x` is `1` if `x ∈ s`, `0` otherwise. -/
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

def y2 : set ℕ := {1,2}
variable {y : set ℕ}
#check set ℕ
#reduce (set ℕ) -- ℕ → Prop
#print y

#reduce 2 ∈ y
#reduce 2 ∈ y2
#reduce y2 19
#print y2
#check y2



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

-- What is `set`?  `set α`?

#print set
/-
@[_ext_core id.{1} name set.ext]
def set : Type u → Type u :=
  λ (α : Type u), α → Prop
-/

#print set.mem
/-
protected def set.mem :
Π {α : Type u}, α → set α → Prop :=
λ {α : Type u} (a : α) (s : set α), s a
-/

#print set.univ 
/-
def set.univ : Π {α : Type u}, set α :=
 λ {α : Type u} (a : α), true
-/

#print ∈
-- _ `∈`:50 _:50 := has_mem.mem #1 #0

#print set.has_mem
/-
 @[instance]
 protected def set.has_mem : Π {α : Type u}, has_mem α (set α) :=
 λ {α : Type u}, {mem := set.mem α}
-/

#print has_mem.mem
/-
@[reducible]
def has_mem.mem : 
  Π {α : Type u} {γ : Type v} [self : has_mem α γ], α → γ → Prop :=
  λ {α : Type u} (γ : Type v) [self : has_mem α γ], [has_mem.mem self]
-/

#check Prop -- Prop: Type
#reduce Prop
#print Prop
#check y → Prop
#reduce y → Prop
#reduce y2 → Prop

#check list -- list: Type u_3 → Type u_3
#check vector -- vector: Type u_3 → ℕ → Type_u_3
#print vector 
/-
 @[_ext_core id.{1} name vector.ext] 
def vector : Type u → ℕ → Type u :=
λ (α : Type u) (n : ℕ), {l // l.length = n}
-/

#print list 
/-
@[_ext_core id.{1} name list.ext]
inductive list : Type u → Type u
constructors:
list.nil : Π {T : Type u}, list T
list.cons : Π {T : Type u}, T → list T → list T
-/

#print set 
/-
@[_ext_core id.{1} name set.ext]
def set : Type u → Type u :=
λ (α : Type u), α → Prop
-/

#print nat
/-
inductive nat : Type
constructors:
nat.zero : ℕ
nat.succ : ℕ → ℕ
-/


#check α
#check α × β 

def tc2 : ℕ × ℕ := (1,2)

#check tc2 

def is_function  (f: set (α × β)) (X:set α) (Y: set β): Prop := 
f ⊆ X.prod Y ∧ ∀x ∈ X,∃!y ∈ Y, (x,y) ∈ f

def Functions (X : set α) (Y: set β): set (set (α × β)) :=
{f | f ∈ 𝒫 (X.prod Y) ∧ (is_function f X Y)}

def Functions2 (X : set α) (Y: set β) :=
{f | f ∈ 𝒫 (X.prod Y) ∧ (is_function f X Y)}

#check Functions2
-- Functions2 : set α → set β → set (set (α × β))

-- set T :=  {x ∈ Univ | x : T}


-- set (ℕ × ℕ) := {x ∈ Univ | x : ℕ × ℕ} where ℕ is nat in Lean
--                ⇔ {x ∈ Univ | x ∈ (N × N)} where N is natural number
-- set (set ( ℕ × ℕ )) := {x ∈ Univ | x: set (ℕ × ℕ)}
--                       ⇔ {x ∈ Univ | x: (N × N)}  -- what is this ??

-- set ℕ := {x ∈ Univ | x : ℕ }
--        ⇔ {x ∈ Univ | x ∈ N}
-- => This is not true `set ℕ` is not a  mathematical set
/- 
 set ℕ := λ x. 
   | true if x : ℕ 
   | false otherwise 
  X := {x ∈ Univ | (set ℕ) x = true}

  set (ℕ × ℕ) := λ x. 
    | true if x : ℕ × ℕ
    | false otherwise
  X := {x ∈ Univ | (set (ℕ × ℕ)) x = true}

  set (set (ℕ × ℕ)) := λ x. 
    | true if x: set (ℕ × ℕ)
    | false otherwise

  set (set (ℕ × ℕ)) := λ x. 
    | true if (set (ℕ × ℕ)) x = true
    | false otherwise
-/
#reduce (set ℕ) 
-- {{1,..∞},{1,..,∞},..}
-- set (set ℕ) := {x ∈ Univ | x : set ℕ}
--              ⇔ {x ∈ Univ | x ∈ 𝒫 (N)} -- Is powerset ???

def setTc2 : set (ℕ × ℕ) := {(1,2),(3,4)}
-- setTc ⊂ ℕ × ℕ

def setSetTc2 : set (set (ℕ × ℕ)) := {{(1,2),(2,3)},{(4,5)}}


-- setSetTc ⊂ 𝒫 (N × N)

def powset2 (A : set Type) : set (set Type) := {x |x ⊂ A}

#check powset2

#check Prop -- Type
#check Type -- Type 1
#check Type 1 -- Type 2
#check Type u -- Type (u+1)
/-
set ℕ
  A ⊂ {x ∈ Univ | (set ℕ) x}
⇔ A ⊂ {x ∈ Univ | ∀y ∈ Univ. y ∈ ℕ}
⇔ A ⊂ {x ∈ Univ | x ∈ ℕ}
⇔ A ⊂ ℕ
--------------------------------
  set (set ℕ)
⇔ set (A ⊂ ℕ)
⇔ S ⊂ {x ∈ Univ | (set (set ℕ)) x}
⇔ S ⊂ {x ∈ Univ | x ∈ (A ⊂ ℕ)}
⇔ 
-/

open set

variable {α₁ : Type*}

#check univ 
#check @univ
#check @univ α
variable {a1 : α₁}

--def a2 : α = x

-- if we 
#check a1 ∈ (@univ α₁)
#reduce a1 ∈ (@univ α₁)  -- true

variables {X₁ Y₁: @univ α}

--
#check {n: ℕ | n ≤ 4} -- set ℕ (it is a subset of ℕ)
#check {n: ℕ // n ≤ 4} -- Type (it is called subtype)
