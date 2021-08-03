/-
Following code are mostly from Logic and Proof:
https://leanprover.github.io/logic_and_proof/functions_in_lean.html

by Jeremy Avigad, Robert Y. Lewis, and Floris van Doorn
-/
universes u v
variables {W X Y Z α β: Sort*}

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

-- The double '{}', ⦃ ⦄ is super important
-- If we write ∀ x₁ : X, ∀ x₂ : X, injective_cmp is not provable
def injective {X Y} (f : X → Y) : Prop :=
  ∀ ⦃ x₁ x₂ ⦄, f x₁ = f x₂ → x₁ = x₂ 

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
--@[reducible] def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

def injective' (f : X → Y) : Prop :=
  ∀ ⦃ x₁ x₂ ⦄, f x₁ = f x₂ → x₁ = x₂

-- We can not write x₁ ∈ X, use x₁ : X instead
def injective2 (f: X → Y) : Prop :=
 ∀ ⦃ x₁ x₂ ⦄, x₁ ≠ x₂ → f x₁ ≠ f x₂

def injective3 (f: X → Y) : Prop :=
 ∀ ⦃ a a' ⦄, a ≠ a' → f a ≠ f a'

def injective4 (f: X → Y) : Prop :=
 ∀ ⦃ a a' ⦄, f a = f a' → a = a'

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

-- Why can not prove this?  Isn't this a tautology?
-- lemma injective_g   {g : Y → Z} 
--                  (Hg: injective g) : injective (g) :=
--assume y₁ y₂,
--assume h: g y₁ = g y₂,
--show y₁ = y₂, from h Hg

-- theorem: if g and f are both injective, g ∘ f is injective
theorem injective_comp {g : Y → Z} {f : X → Y}
    (Hg : injective g) (Hf : injective f) : injective (g ∘ f) :=
assume x₁ x₂ : X,
--assume y₁ y₂ : Y, -- This ': Y' is necessary for the following 
--assume  h2: g y₁ = g y₂,
--have y₁ = y₂, from h2 Hg,
assume h1 : (g ∘ f) x₁ = (g ∘ f) x₂,
-- If f x₁ = f x₂ → x₁ = x₂ from Hf
-- If g x₂ = g x₂ → x₁ = x₂ from Hg
-- If (g ∘ f) x₁ = (g ∘ f) x₂ → x₁ = x₂ 
-- How to prove the following prop?
--  If (g ∘ f) x₁ = (g ∘ f) x₂ → f x₁ = f ×2
-- Since g x₁ = g x₂ → x₁ = x₂ by Hg
-- ALso f ×₁ = f x₂ → x₁ = x₂ by Hf
have f x₁ = f x₂, from Hg h1,
show x₁ = x₂, from Hf this 

example (q r : Prop) : q ∧ r → q :=
assume h: q ∧ r,
have r, from and.right h, 
show q, from and.left h

#check Type




variable U : Type 
variable P : U → Prop
variable Q : Prop 
-- introduce a new variable y and prove Q
-- under the assumption that P y holds.
example (h1 : ∃ x, P x) (h2: ∀ x, P x → Q) : Q :=
exists.elim h1
  (assume (y : U) (h: P y),
    have h3 : P y → Q, from h2 y,
    show Q, from h3 h)


example (h1: ∃ x, P x) (h2: ∀ x, P x → Q) : Q :=
exists.elim h1 (assume y h, h2 y h)

example (h1: ∃ x, P x) (h2: ∀ x, P x → Q) : Q :=
exists.elim h1 $
assume y h, h2 y h

--def surjective (f: X → Y) : Prop :=
-- ∀ y, ∃ x, f x = y
-- What is "$"?
--   -> It is a syntax suger of '( some proof )'
theorem surjective_comp {g : Y → Z} {f: X → Y}
  (hg: surjective g) (hf: surjective f) :
  surjective (g ∘ f) :=
  assume z,
  exists.elim (hg z) $
  assume y (hy : g y = z),
  exists.elim (hf y) $
  assume x (hx : f x = y),
  have g (f x) = z, from eq.subst (eq.symm hx) hy,
  show ∃ x, g (f x) = z, from exists.intro x this

