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
variables {A B C: set α}
 
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
--def test_pwset : set (ℕ × ℕ) := {f ∣ f ∈ powerset {v2 × v2}}
--#reduce {f:nat × nat ∣ f ∈ powerset {v2 × v2}}
-- #check {n  ∣ n ∈ ℕ}
--#reduce {f ∣ f ∈ powerset {v2 × v2}}
-- v = {1,2}, v2 = {2,3}
-- v × v2 = {(1,2),(1,3),(2,2),(2,3)}
-- powerset v × v2 = {∅,
--                    {(1,2)}, {(1,2),(1,3)},{(1,2),(2,2)},{(1,2),(2,3)},
--                    {(1,3),(2,2)}, {(1,3),(2,3)},
--                    {(2,2),(2,3)},
--                    {(1,2),(1,3),(2,2)},{(1,2),(2,2),(2,3)},
--                    {(1,3),(2,2),(2,3)},
--                    {(1,2),(1,3),(2,2),(2,3)}}