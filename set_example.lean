import data.set 
-- import data.nat.basic
-- import set_theory.cardinal

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
#reduce (a, b).1
#reduce (a, b).2
#check [1, 2] -- list ℕ 
#check [a,b] -- List (Type u)
--instance i: (x: nat) (y: nat) := ⟨1, 2⟩
def v : set nat := {1,2}
#check v 

def v2 : set nat := {2, 3}

def v3: set (ℕ × ℕ)  := {(1,2), (2,4)}

#reduce (1,2) ∈ v3
#reduce powerset v2
#reduce v × v2
-- #reduce (1,2) ∈ set(v × v2)
#reduce 1 ∈ v2
#reduce 2 ∈ v
#eval 2 ∈ v
