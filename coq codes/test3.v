Require Import List.
Require Import Arith.
Require Import Bool.

Lemma n1 : forall x : nat, 1 + x = S x.
Proof.
trivial. Qed.

Definition n2 : forall x y : nat, S x + y = S(x + y).
Proof.
Admitted. 
(* Use Admitted so that we can work on more difficult asserts
before. We can search in built theorems that prove
the "trivialities".*)



Require Import List.
Require Import Arith.
Require Import Bool.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat div prime. 

Notation "x | y" := (y mod x = 0)
(at level 50, left associativity).

Lemma one_div_all_nat : forall n : nat, 1 | n.
Proof.
intro. simpl. reflexivity. Qed.

Lemma k_div_k_times_n : forall (k n : nat), (k > 0) -> (k | n*k).
Proof.
intros.
induction k as [|k']. 
  trivial.
Admitted.

(* A nice proof of the infinitude of primes, by Georges Gonthier *)
Lemma infinite_prime_above m : {p | m < p & prime p}.
Proof. 

have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1
  by rewrite addn1 ltnS fact_gt0.

exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.

by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.




 

 