Require Import List.
Require Import Arith.
Require Import Bool.
From Coq Require Import ssreflect ssrfun ssrbool.
(*From mathcomp Require Import eqtype ssrnat div prime. 
From Coq Require Import Reals.Reals.*)

Notation "x | y" := (y mod x = 0)(at level 40, left associativity).

Goal forall n:nat, exists x, x=n.
Proof.
  intros.
  refine(ex_intro _ (n) _).
  reflexivity.
Qed.

Goal forall n:nat, exists x, x>n.
Proof.
  intros.
  refine(ex_intro _ (S n) _).
  intuition.
Qed.

Goal forall (n:nat), exists x:nat, n>1 -> x <S n.
Proof.
  intros.
  refine(ex_intro _ n _).
  intros.
  intuition.
Qed.

Goal forall n, n + 0 = n.
Proof.
induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Goal forall n m, n + m = m + n.
Proof.
  intros.
  induction n.
    elim m.
      intros.
      reflexivity.
      intros.
      simpl.
      rewrite <- H.
      simpl.
      reflexivity.
    simpl.
    rewrite IHn.
    elim m.
    simpl.
    reflexivity.
    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Goal forall x y z,  (x + y) + z = x + (y + z).
Proof.
  intros.
  elim x.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.

Goal forall x y z, (x + y) * z = x * z + y * z.
Proof.
  intros.
  elim x.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite H.

  assert(forall a b c,  (a + b) + c = a + (b + c)).
  intros.
  elim a.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite <- H0.
  reflexivity.

  case H0.
  reflexivity.
Qed.

Goal forall m n, m * n = n * m.
Proof.
  intros m n.
  elim m.
    simpl.
    elim n.
      simpl.
      reflexivity.
      intros m' H1.
      simpl.
      case H1.
      reflexivity.
    intros m' H2.
    simpl.
    rewrite H2.
    elim n.
      simpl.
      reflexivity.
    intros n' H3.
    simpl.
    
    assert(forall n m, n = m -> S n = S m).
    auto.
    apply H.
    
    rewrite <- H3.
    
    assert(forall x y, x + (y + x*y) = y + (x + x*y)).
    intros x y.
    elim x.
        simpl.
        reflexivity.
    intros n0 H5.
    simpl.
    rewrite H5.
    elim y.
      simpl.
      reflexivity.
      intros n1 H6.
      simpl.
      apply H.
      
      assert(forall a b c d, a + b = c + d -> a + S b = c + S d).
      intros.
      apply eq_add_S.
      assert(forall a b, a + S b = S(a+b)). auto.
      rewrite H1.
      rewrite H1.
      apply H.
      apply H.
      exact H0.

      apply H0.
      
      (*
      assert(forall a b c d, a+(b+S(c)) = b+S d -> a+S(c) = S d).
      intros a b c d.
      intros H7.
      assert(forall a , a + S c = S(a+c)). auto.
      rewrite H1.
      apply H.*)

      
      
      
      
      admit.
    
    case H0.
    reflexivity.
Admitted.


      








