Require Export Poly.

Theorem double_injective':
  forall n m, double n = double m -> n = m.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0". simpl. intros m eq.
  destruct m as [|m'].
  SCase "m = 0". reflexivity.
  SCase "m = S m'". inversion eq.
  Case "n = S n'".
  intros m eq.
  destruct m as [|m'].
  SCase "m = 0".
  inversion eq.
  SCase "m = S m'".
  assert (n' = m') as H.
  SSCase "Proof os assertion".
  apply IHn'.
  inversion eq. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem double_injective_take2:
  forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  Case "m=0". simpl. intros n eq. destruct n as [|n'].
  SCase "n=0". reflexivity.
  SCase "n= S n'". inversion eq.
  Case "m= S m'". intros n eq.
  destruct n as [|n'].
  SCase "n = 0". inversion eq.
  SCase "n = S n'".
  assert (n' = m') as H.
  SSCase "Proof of assertion".
  apply IHm'.
  inversion eq.
  reflexivity.
  inversion H.
  reflexivity.
Qed.

Theorem plus_n_n_injective_take2:
  forall n m, n + n = m + m -> n = m.
Proof.
  intros.
  generalize dependent n.
  induction m as [|m'].
  Case "m=0".
  destruct n as [|n'].
  SCase "n=0". reflexivity.
  SCase "n=S n'". intro. inversion H.
  Case "m=S m'".
  intros.
  destruct n as [|n'].
  SCase "n = 0".    inversion H.
  SCase "n = S n'".
  rewrite <- plus_n_Sm in H.
  rewrite <- plus_n_Sm in H.
  apply eq_remove_S.
  apply IHm'.
  inversion H.
  reflexivity.
Qed.

Theorem index_after_last:
  forall (n:nat) (X:Type) (l :list X), length l = n -> index (S n) l = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [|l0 l'].
  Case "l=[]".
  simpl. intros. reflexivity.
  Case "l=l0:l'".
  simpl. intros.
  rewrite <- H.
  apply IHl'.
  reflexivity.
Qed.


Theorem length_snoc''':
  forall (n : nat) (X : Type) (v : X) (l : list X),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros.
  generalize dependent n.
  induction l as [| l0 l'].
  Case "l=[]".
  simpl. intros. rewrite <- H. reflexivity.
  Case "l=l0::l'".
  simpl. intros. apply eq_remove_S in H. rewrite <- H.
  apply eq_remove_S.
  apply IHl'.
  reflexivity.
Qed.

Theorem app_length_cons:
  forall (X:Type) (l1 l2:list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
Proof.
  intros.
  generalize dependent n.
  generalize dependent l2.
  induction l1 as [|n0 l1'].
  Case "l1=[]".
  simpl. intros. apply H.
  Case "l1=n0 l1'".
  simpl. intros. rewrite <- H.
  apply eq_remove_S. apply IHl1'.
  reflexivity.
Qed.

Theorem app_length_twice:
  forall (X:Type) (n:nat) (l:list X),
    length l = n -> length (l ++ l) = n + n.
Proof.
  intros.
  generalize dependent n.
  induction l as [|n0 l'].
  Case "l=[]".
  simpl. intros. rewrite <- H. reflexivity.
  Case "l=n0:l'".
  intros. destruct n.
  SCase "n = 0".
  inversion H.
  SCase "n = S n'".
  simpl.
  remember (length (l' ++ n0 :: l')) as nn.
  symmetry in Heqnn.
  apply app_length_cons in Heqnn.
  rewrite <- Heqnn.
  rewrite <- plus_n_Sm.
  assert (length (l' ++ l') = n + n) as H1.
  inversion H.
  apply IHl'. reflexivity.
  rewrite H1.
  reflexivity.
Qed.