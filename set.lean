import data.set
open set

variable {U : Type}
variables A B C : set U
variable x : U

example : A ∩ A = A :=
eq_of_subset_of_subset
(assume x,
 assume h: x ∈ (A ∩ A),
 show x ∈ A, from and.left h)
(assume x,
 assume h: x ∈ A,
 show x ∈ (A ∩ A), from and.intro h h)

example : A ∪ A = A :=
eq_of_subset_of_subset
(assume x,
 assume h: x ∈ A ∪ A,
 have o1: x ∈ A ∨ x ∈  A, from h,
 show x ∈ A, from or.elim o1
 (assume a1: x ∈ A,
  show x ∈ A, from a1)
 (assume a2: x ∈ A,
  show x ∈ A, from a2)
)
(assume x,
 assume h: x ∈ A,
 show x ∈ (A ∪ A),from or.inl h) -- or.inl := or introducition left


example : A ∪ (∅: set U) = A :=
eq_of_subset_of_subset
(assume x,
 assume h: x ∈ A ∪ ∅,
 have h2: x ∈ A ∨ x ∈ (∅: set U), from h,
 show x ∈ A, from or.elim h2
  (assume h2_1: x ∈ A,
   show x ∈ A, from h2_1)
  (assume h2_2: x ∈ (∅: set U),
   show x ∈ A, from false.elim h2_2 --> x ∈ ∅ = false, so false -> anything
  )
)
(assume x,
assume h: x ∈ A,
show x ∈ A ∪ ∅, from or.inl h)