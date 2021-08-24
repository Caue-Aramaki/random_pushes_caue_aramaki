Definition example1 := fun x : nat => x*x+2*x+1.
Compute example1 1.

Definition example2 (x : nat) := x*x+2*x+1.
Compute example2 1.

Require Import Bool.
Compute if true then 3 else 5.

Require Import Arith.
Definition is_zero (n:nat) :=
match n with
0 => true
| S p => false
end.



Fixpoint sum_n n :=
match n with
0 => 0
| S p => p + sum_n p
end.

Compute sum_n 10.



Fixpoint is_even (n:nat) :=
match n with
| 0 => true
| 1 => false
| S (S p) => is_even p
end.

Compute is_even 4.




Definition better_sum_n (n:nat) :=
match n with
n => n * (n + 1) / 2
end.

Compute better_sum_n 10.




Require Import List.

Check 1::2::3::nil.

Compute map (fun x => x + 3) (1::3::2::nil).

Definition square n :=
match n with
n => n*n
end.

Compute map square (1::2::3::4::5::nil).





SearchPattern (nat -> nat -> bool).

Search Nat.eqb.

Locate "_ =? _".

Compute Nat.eqb 3 3.
Compute Nat.eqb 3 4.

Compute let l := (1::2::nil) in l.


Require Import List.

Fixpoint first_n_aux (n:nat)(m:nat) :=
match n with 
|0 => nil 
| S p => m :: first_n_aux p (m+1) 
end.

Definition first_n (n:nat) := first_n_aux n 0.

Compute first_n 10.




