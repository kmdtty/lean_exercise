/-
Definition and propositions on Image

from Takesi, Saito "Syugo to Iso" (2009)
-/ 
import data.set 
import data.set.basic

variables {α β: Type*}
variable {X: set α}
variable {Y: set β}

open set 

def is_transitive (R: α × α → Prop) : Prop :=
  sorry

def is_reflexive (R: α × α → Prop) : Prop :=
  sorry 

def is_symmetry (R: α × α → Prop) : Prop :=
  sorry 

def eq_relation (f: α → β) (a: α × α) : Prop :=
  f a.1 = f a.2

/-
Propsition 2.6.1 (1)

The relation Rf by the equivalence of function:
f(x) = f(x') is a equivalence relation.
-/
def is_equiv_relation (R: α × α → Prop): Prop :=
  is_reflexive(R) ∧ is_symmetry(R) ∧ is_transitive(R) 

theorem equality_relation_of_f_is_equiv_relation {f: α → β}:
 is_equiv_relation (eq_relation f) := sorry

def graph (R: α × α → Prop) : set(α × α) :=
  {a : α × α | R a}

def diagonal (s : set β) : set (β × β) :=
  {b ∈ (s.prod s) | b.1 = b.2}

variable f': α → β 
#check range f'

/--
This function fxf is supposed to use with currying.

eg.
#check fxf f
-> fxf f' : α × α → β × β
-/
def fxf (f: α → β) (a: α × α) : β × β :=
  ⟨f a.1, f a.2⟩ 

#check fxf f'


--#eval {(f' x.1, f' x.2) ∈ Y.prod Y | x ∈ X.prod X}
/-
Proposition 2.6.1 (2-a)

The graph of the relatio Rf is equivalent with inverse
image of the diagnal set of Y (Δy)
-/
theorem graph_of_eq_relation_f_is_inverse_image_of_diagonal_set 
{f : α → β}:
graph (eq_relation f) = preimage (fxf f) (diagonal (range f))
 :=  sorry