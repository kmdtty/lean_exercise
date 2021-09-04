/-
Theorems/Examples from Fuichi, Uchida "Shugo to Iso" (2020).
-/

universes u v
-- What's the difference between:
-- Sort, Sort*, Type, Type* ?
variables {A B C W X Y Z α β: Sort*}

--def injective {X Y} (f : X → Y) : Prop :=
--  ∀ ⦃ x₁ x₂ ⦄, f x₁ = f x₂ → x₁ = x₂ 

def injective (f: X → Y) : Prop :=
 ∀ ⦃ x₁ x₂ ⦄ , f x₁ = f x₂ → x₁ = x₂

--@[reducible] def injective (f : α → β) : Prop := 
--∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

def surjective (f: X → Y) : Prop :=
 ∀ y, ∃ x, f x = y

theorem injective_id : injective(@id X) :=
assume x₁ x₂,
assume h1: id x₁ = id x₂,
show x₁ = x₂, from h1

--theorem injective_comp {f: X → Y} {g: Y→ Z}
--(hg: injective f) (hg: injective g) :
--injective (g ∘ f) :=
--sorry

/--
 Theorem 6.1: 
  Let f: A → B, g : B → A,
  f ∘ g = id B → surgective f ∧ injective g. 
-/
theorem id_comp_surj
  {f: A → B} {g: B → A} : 
  f ∘ g = @id B →  surjective f  :=
assume h1: f ∘ g = @id B,
assume b₁ : B,
-- congr_fun is a congruence rule for the simplifier, see:
-- https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html#equality
have h2: f (g b₁) = id b₁, from congr_fun h1 b₁,
let a := g b₁ in
show ∃ a, f(a) = b₁, from exists.intro a h2
/-
let a := g b₁ in
show ∃ a, f(a) = b₁, from exists.intro a h2
-/


theorem id_comp_injective
{f: A → B} {g: B → A} :
f ∘ g = @id B → injective g :=
assume h1: f ∘ g = @id B,
assume b₁ b₂ : B,
assume h2: g b₁ = g b₂,
have h3: f (g b₁) = f (g b₂), from congr_arg f h2,
have h4: f (g b₁) = id b₁, from congr_fun h1 b₁,
have h5: f (g b₂) = id b₂, from congr_fun h1 b₂,
have h6: id b₁ = f (g b₂), from eq.subst h4 h3,
have h7: id b₁ = id b₂, from eq.subst h5 h6,
show b₁ = b₂, from h7
--have id b₁ = f (g b₂), by rw [←h3, h4],
--by rw [←h3,h4,←h5],
--show b₁ = b₂, by rewrite [h5,h4,h3]

/-
Exercise 6.2
Let f: A→B, g: B→C
(1) If g ∘ f is injective, f is injective
(2) If g ∘ f is surjective, g is surjective
-/

-- (1)
theorem comp_injective_1st 
{f: A → B} {g: B → C} :
injective (g ∘ f) → injective f :=
assume h1: injective (g ∘ f),
assume a₁ a₂ : A,
assume h4: f a₁ = f a₂,
-- We can not say the following equality on the image of the function g
-- unless using congr_arg.
-- have h5: g (f a₁) = g (f a₂), from  h4,
have h5: g (f a₁) = g (f a₂), from congr_arg g h4,
show a₁ = a₂, from h1 h5 

--(2)
theorem comp_surjective_2nd
{f: A → B} {g: B → C} :
surjective(g ∘ f) → surjective g :=
assume h1: surjective (g ∘ f),
have h2: ∀c:C, ∃a:A, g (f a) = c, from h1,
assume a : A,
let b := f a in
show ∀c:C, ∃b:B, g (b) = c, from exists.intro b h2
/-
exists.elim h2
(assume a₁,
 assume ha: ∀c, g (f a₁) = c,
 let b := f a₁ in
 show ∀c, ∃b, g (b) = c, from exists.intro b ha)
-/

