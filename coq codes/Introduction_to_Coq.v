Require Import List.
Require Import Arith.
Require Import Bool.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat div prime. 
(*Imports, check "lib" folder.*)

(*Inductive nat : Set :=
| O : nat
| S : nat -> nat.*)

Print nat.

Eval compute in 0.
Eval compute in S(O). (*1*)

Fixpoint add(a b :nat) : nat :=
  match a with
  | 0 => b
  | S n => S(add n b)
end.

Compute add 1 3.

Theorem add_assoc : forall (a b c : nat), 
  (add a (add b c)) = (add (add a b) c).
Proof. (*Begin proof*)
  intros a b c. (*Introduce a b c as "given".*)
  induction a as [|n].  (*Induction on a, as n.*)
    simpl. reflexivity. (*Base case*)
    simpl. rewrite -> IHn. reflexivity. (*General case*)
Qed. (*Begin proof*)

Print add_assoc.

Print nat_ind.

Theorem one_not_eq_two : ~ 1 = 2.
Proof.
unfold not. 
intros H.
inversion H.
Qed.

Theorem n_geq_zero : ~ 0 > 0.
Proof.
unfold not. unfold gt. unfold lt.
intros H.
inversion H.
Qed.

Definition pred (n : nat) : n > 0 -> nat :=
  match n with
  | O => fun pf => match (n_geq_zero pf) with end
  | S n' => fun _ => n'
end.

Theorem one_exists : exists (n : nat), n = 1.
Proof.
exists 1. reflexivity.
Qed.

Eval compute in pred 3.


Notation "x | y" := (y mod x = 0)
(at level 50, left associativity).
