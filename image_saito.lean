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

/-
Propsition 2.6.1 (1)

The relation Rf by the equivalence of function:
f(x) = f(x') is a equivalence relation.
-/
def is_equiv_relation (R: α × α → Prop): Prop :=
  is_reflexive(R) ∧ is_symmetry(R) ∧ is_transitive(R) 

theorem Rf_is_equiv_relation {Rf: α × α → Prop}:
 is_equiv_relation(Rf) := sorry

def graph_of_relation (R: α × α → Prop) : set(α × α) :=
sorry 

/-
Proposition 2.6.1 (2-a)

The graph of the relatio Rf is equivalent with inverse
image of the diagnal set of Y (Δy)
-/
theorem Rf_graph_is_inverse_image_of_diagonal_set 
{Rf: α × α → Prop} {f: α × α → β × β} {Δy : set(β × β)}:
 graph_of_relation(Rf) = preimage f Δy
 := sorry