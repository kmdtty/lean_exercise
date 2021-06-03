import data.set
open set

variable {U : Type}
variables A B C : set U
variable x : U

-- not yet proved
example : A ∪ A = A :=
eq_of_subset_of_subset
(assume x,
 assume h: x ∈ A,
 show x ∈ (A ∪ A),from or.inl h)
(assume x,
 assume h: x ∈ (A ∪ A),
 have h1: x ∈ A ∨ x ∈ A, from h,
 or.elim h
 (assume hal: x ∉ A
  show x ∈ A,from h1 hal)
 (assume har: x ∉ A,
  show x ∈ A, from h1, har)


