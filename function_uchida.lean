/-
Theorems/Examples from Fuichi, Uchida "Shugo to Iso" (2020).
-/

universes u v
variables {A B W X Y Z α β: Sort*}

def surjective (f: X → Y) : Prop :=
 ∀ y, ∃ x, f x = y
-- What is "$"?
--   -> It is a syntax suger of '( some proof )'

  /--
   Theorem: 
   Let f: A → B, g : B → A,
   f ∘ g = id B → surgective f ∧ injective g. 
  -/
theorem id_comp_surj_inj 
  {f: A → B} {g: B → A} : 
  f ∘ g = (@id B) → surjective (f ∘ g) := --surjective f ∧ injective g:=
assume a : A,
assume b₁ (hb1: g b₁ = a),
assume b₂ (hb2: (f ∘ g) b₁ = b₂),
assume h1: (f ∘ g) b₁ = id b₂,
have h2: f (g b₁) = b₂, from h1,
show ∃ b₁, f (g b₁) = b₂, from exists.intro b₁ h2
-- have h3: b₁ = b₂, from