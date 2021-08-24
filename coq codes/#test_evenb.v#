
(*let evenb be a function := nat -> bool,
with evenb(2n) = true, evenb(2n+1) = false.

Problems:
Prove definition a1.
Prove definition a2.*)


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

(*you may create any inductive types or even edit the
main function, as long as it outputs correctly and the goal
remains unchanged.*)

(*Notations.*)


(*Here starts definitions/exercises*)

Definition a0 : forall b:bool, negb b <> b.
Proof.
  intro b.
  autounfold.
  case b.
    simpl. intro. discriminate.
    simpl. intro. discriminate.
Qed.

Definition a0_1 : forall b:bool, b <> negb b.
Proof.
  intro b.
  autounfold.
  case b.
    simpl. intro. discriminate.
    simpl. intro. discriminate.
Qed.

Definition a1 : forall (n:nat), 
  evenb n = evenb (n+2).
Proof.
  (*insert proof here*)
Admitted.

Definition a2 : forall (n:nat),
  evenb n = negb (evenb(n+1)).
Proof.
  (*insert proof here*)
Admitted.

Definition a2_1 : forall (n:nat), evenb n <> evenb(n+1).
Proof.
  intro.
  pose proof a2 as a2.
  rewrite a2.
  pose proof a0 as a0.
  apply a0.
Qed.

Definition a2_2 : forall n:nat, 
evenb n = negb (evenb (n + 1)) <-> evenb n <> evenb(n+1).
Proof.
  intro.
  unfold iff.
  refine(conj _ _).

    intro.
    rewrite H.
    pose proof a0 as a0.
    apply a0.

    intro.
    autounfold in H.
    (*                    did not work for me.
    destruct H as [].
    pose proof a2 as a2.
    rewrite a2.
    pose proof a0 as a0.
    
    pose(x := evenb(n+1)).
    assert(x = evenb(n+1)).
    auto.
    rewrite <- H.
    case x.
      simpl.
      assert(false <> true). intuition. discriminate.*)
    pose proof a2.
    apply H0.
Qed.

Goal 6 = 6.
Proof.
  assert(forall x:nat, x = x). reflexivity.
  pose(x := 6).
  assert(6 = x). trivial.
  rewrite H0.
  apply H.
Qed.
  

Goal evenb 4 = evenb 6.
Proof.
  pose proof a1 as hyp_1.
  apply hyp_1.
Qed.

Goal evenb 4 = evenb 820.
Proof.
  pose proof a1 as hyp_1.
  apply hyp_1.
Qed.

Goal evenb 4 <> evenb 5.
Proof.
  pose proof a2_1 as hyp_2.
  apply hyp_2.
Qed.

Goal evenb 7 = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem two_n_is_even : forall n:nat, evenb(2*n) = true.
Proof.
  intro.
  elim n. simpl. reflexivity.
    intros.
    pose proof a1.
    rewrite H0 in H.
    assert(2* S n0 = 2*n0 + 2). auto.
    rewrite H1.
    exact H.
Qed.

Theorem a3_1 : forall n:nat, evenb(2*n + 1) = false.
Proof.
  intro.
  pose proof two_n_is_even as lem1.
  pose proof a2 as lem2.
  
  assert(forall n : nat, 
      evenb (2*n) = negb (evenb (2*n + 1))).
    intro.
    pose(x:=2*n0).
    assert(2*n0 = x). auto.
    rewrite H.
    apply lem2.
  
    assert(negb(evenb (2 * n + 1)) = true).
    rewrite <- H.
    apply lem1.
    
    assert(forall b:bool, negb b = true -> b = false).
    intro b.
    case b.
      auto.
      auto.
    
    pose(x:=2 * n + 1). assert(x = 2 * n + 1). auto.
    rewrite <- H2.
    assert(negb(evenb(x)) = true).
    rewrite H2.
    exact H0.
    apply H1.
    exact H3.
Qed.




