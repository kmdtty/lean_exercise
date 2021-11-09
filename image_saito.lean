/-
Definition and propositions on Image

from Takesi, Saito "Syugo to Iso" (2009)
-/ 
variables {α β: Type*}
variable {X: set α}
variable {Y: set β}

def is_transitive (R: α × α → Prop) : Prop :=
  sorry

def is_reflexive (R: α × α → Prop) : Prop :=
  sorry 

def is_symmetry (R: α × α → Prop) : Prop :=
  sorry 

def is_equiv_relation (R: α × α → Prop): Prop :=
  is_reflexive(R) ∧ is_symmetry(R) ∧ is_transitive(R) 

theorem Rf_is_equiv_relation {Rf: α × α → Prop}:
 is_equiv_relation(Rf) := sorry