Require Import List.
Fixpoint first_n_aux (n:nat)(m:nat) :=
match n with 0 => nil | S p => m :: first_n_aux p (m+1) end.
Definition first_n (n:nat) := first_n_aux n 0.

Search True.
Locate "_ =? _".
Locate "_ -> _".




Require Import List.
Require Import Arith.
Require Import Bool.


Fixpoint is_even_aux (n:nat) :=
match n with
| 0 => 0
| 1 => 1
| S (S p) => is_even_aux p
end.

Definition is_even (n:nat) := is_even_aux n.

Definition over_two : forall x : nat,
is_even(x) = is_even(x+2).
Proof.
assert (forall x : nat, is_even(x) = is_even(S(S(x)))). trivial.

assert (forall x: nat, x+2 = S(S(x)) -> x+2 = x+2). trivial.

assert (forall x: nat, x+2 = S(S(x)) -> is_even (x+2) = is_even (S (S x))).
firstorder.

assert (forall x : nat, is_even (x + 2) = is_even (S (S x)) 
-> is_even x = is_even (x + 2)).
firstorder.

assert (forall x : nat, x + 2 = S (S x)).



  




