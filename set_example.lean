import data.set 
-- import set_theory.zfc 
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
#check A.prod B
-- not yet defined
def set_of_function {f: A → B}: set (set (α × β)) :=
{sf | sf ∈ 𝒫 (A.prod B) -- ∧ is_function(sf)
}

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
