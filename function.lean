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

def injective3 (f: X → Y) : Prop :=
 ∀ a a' : X, a ≠ a' → f a ≠ f a'

def injective4 (f: X → Y) : Prop :=
 ∀ a a' : X, f a = f a' → a = a'

-- We can eliminate writing :Y, :X
def surjective (f: X → Y) : Prop :=
 ∀ y, ∃ x, f x = y

def bijective (f: X → Y) := injective f ∧ surjective f 

/--
 What is @id mean?
 @ is for preventing to fill implicit argument 
 and forcing to fill statement.
 ... what?

 If we get rid of @ from "@id", lean raises type
 error anyway.
--/

/- 
Let's prove identity function is injective.

The syntax of injective proposition is defined with
def injective (f: X → Y) : Prop 
So "injective (@id X)" means, 
given function id with domain X, it is injective.
-/
theorem injective_id : injective (@id X) :=
assume x₁ x₂,
assume H : id x₁ = id x₂,
show x₁ = x₂, from H -- prove this from def of id

theorem injective_id3 : injective3 (@id X) :=
assume a a',
assume H : a ≠ a',  -- contraposition can not be proved automatically
show id a ≠ id a', from H 

theorem injective_id4 : injective4 (@id X) :=
assume a a',
assume H : id a = id a',
show a = a', from H 

-- prove identity function is subjective
theorem surjective_id : surjective (@id X) :=
assume y,
show ∃ x, id x = y, from exists.intro y rfl

-- prove identy function is bijective 
theorem bijective_id : bijective(@id X) :=
and.intro injective_id surjective_id

-- prove compisition of injective functions
-- is injective

theorem injective_comp {g : Y → Z} {f : X → Y}
    (Hg : injective g) (Hf : injective f) :
    injective (g ∘ f) :=
assume x₁ x₂,
assume : (g ∘ f) x₁ = (g ∘ f) x₂,
have f x₁ = f x₂, from Hg this,
show x₁ = x₂, from Hf this 
