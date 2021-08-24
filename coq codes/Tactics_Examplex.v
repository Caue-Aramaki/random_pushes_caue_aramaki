Goal forall p:Prop, p -> p.
Proof.
  intros.
  assumption.
Qed.

Goal 41 + 3 = 44.
Proof.
 reflexivity.
Qed.

Goal forall p:Prop, p -> p.
Proof.
  info_trivial.
Qed.

Goal forall (P Q : Prop),
  (P -> Q) -> ~Q -> ~P.
Proof.
  info_auto.
Qed.

Inductive el :=
| grass : el
| fire : el
| water : el.

Goal fire <> water.
Proof.
  discriminate.
Qed.

Goal forall P : Prop,
  0 = 1 -> P.
Proof.
  intros.
  discriminate.
Qed.

Goal 69 = 69 -> 69 = 69.
Proof.
  intro.
  exact H.
Qed.

Goal forall (P Q : Prop),
  P /\ ~P -> Q.
Proof.
  intros.
  destruct H as [].
  contradiction.
Qed.

(* ctrl D adds a comment
   ctrl F finds expression
 *)

Goal forall (P Q : Prop),
  (P -> Q) -> ~Q -> ~P.
Proof.
  intros.
  unfold not.
  intros.
  pose(f:= H H1).
  contradiction.
Qed.

Definition plus_two (x : nat) : nat :=
  x + 2.

Goal
  plus_two 2110 = 2112.
Proof.
  unfold plus_two.
  simpl.
  reflexivity.
Qed.

Goal forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  unfold not.
  unfold not in H.
  refine(conj _ _).
  intro.
  auto.
  auto.
Qed.

Goal forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  intros.
  apply H.
  exact H0.
Qed.

Goal forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  intros.
  apply H in H0.
  exact H0.
Qed.

Goal forall (P Q:Prop),  P -> (P -> Q) -> Q.
Proof.
  repeat intro.  
  assert(P -> (P -> Q) -> Q).
  auto.
  apply H1.
  auto.
  auto.
Qed.

Goal forall (x y : nat),
  x + y = y + x.
Proof.
  repeat intro.
  induction x.
  simpl.
  induction y.
  reflexivity.
  simpl.
  rewrite <- IHy.
  reflexivity.
  simpl.
  rewrite -> IHx.
  trivial.
Qed.

Goal forall (x y : nat),
  S x = S y -> x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Goal forall (P Q : Prop),
  P -> P \/ Q.
Proof.
  intros.
  left.
  assumption.
Qed.

Goal forall (x : nat),
  1 + x + 1 = 2 + x.
Proof.
  intro. simpl.
  replace (x + 1) with (S x). 
  reflexivity.
  
  assert(1 + x = S x).
  simpl.
  reflexivity.
  rewrite <- H.
  
  elim x.
  reflexivity.
  intros.
  simpl.
  rewrite <- H0.
  simpl.
  reflexivity.
Qed.

Goal forall (P Q R : Prop),
  P -> (P -> Q) -> (P -> R) -> (Q /\ R).
Proof.
  intros.
  split.
  apply H0 in H.
  exact H.
  apply H1 in H.
  exact H.
Qed.

Goal forall (P Q : Prop),
  (P /\ Q) -> P.
Proof.
  intros.
  destruct H.
  exact H.
Qed.

Inductive element :=
| weed : element
| bolt : element
| hydro : element.

Definition weakness (e : element) : element :=
  match e with
  | weed => bolt
  | bolt => hydro
  | hydro => weed
  end.

Goal forall (e : element),
  weakness e <> e.
Proof.
  destruct e.
  unfold weakness.
  discriminate.
  unfold weakness.
  discriminate.
  unfold weakness.
  discriminate.
Qed.

Goal forall (n : nat),
  n + n = n * 2.
Proof.
  induction n as [| x IH].
  simpl.
  reflexivity.
  simpl.
  rewrite <- IH.
  replace (x + S x) with (S(x+x)).
  reflexivity.
  simple apply plus_n_Sm.
Qed.

Require Import Arith.

Theorem foil : forall a b c d,
  (a + b) * (c + d) = a*c + b*c + a*d + b*d.
Proof.
  intros. ring.
Qed.

Theorem demorgan : forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.

Theorem and_comm : forall (P Q : Prop),
  P /\ Q -> Q /\ P.
Proof.
  intros P Q P_and_Q.
  destruct P_and_Q. 
  split; assumption.
Qed.






  









