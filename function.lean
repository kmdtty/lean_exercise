/-
Following code are mostly from Logic and Proof:
https://leanprover.github.io/logic_and_proof/functions_in_lean.html

by Jeremy Avigad, Robert Y. Lewis, and Floris van Doorn
-/
variables {W X Y Z : Type}

/-
def comp (f : Y → Z) (g: X → Y) : X → Z :=
λx, f(g x)

infixr ` ∘ ` := comp

def id (x: X) : X := 
x
-/
-- funext is function extensionality (what?)
example (f g : X → Y) (h: ∀ x, f x = g x) : f = g:=
funext h 

-- rfl is reflexivity
lemma left_id (f : X → Y) : id ∘ f = f := 
rfl

lemma right_id (f: X → Y) : f ∘ id = f := 
rfl

theorem comp.assoc (f: Z → W) (g: Y → Z) (h: X → Y) :
(f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

theorem comp.left_id (f: X → Y) : id ∘ f = f := rfl

theorem comp.right_id (f: X → Y) :f ∘ id = f := rfl

def injective (f : X → Y) : Prop :=
  ∀ x₁ : X, ∀ x₂ :X , f x₁ = f x₂ → x₁ = x₂

-- We can not write x₁ ∈ X, use x₁ : X instead
def injective2 (f: X → Y) : Prop :=
 ∀ x₁ : X, ∀ x₂ :X, x₁ ≠ x₂ → f x₁ ≠ f x₂

-- We can eliminate writing :Y, :X
def surjective (f: X → Y) : Prop :=
 ∀ y, ∃ x, f x = y

def bijective (f: X → Y) := injective f ∧ surjective f 

theorem injective_id : injective (@id X) :=
assume x₁ x₂,
assume H : id x₁ = id x₂,
show x₁ = x₂, from H

theorem surjective_id : surjective (@id X) :=
assume y,
show ∃ x, id x = y, from exists.intro y rfl

theorem bijective_id : bijective(@id X) :=
and.intro injective_id surjective_id