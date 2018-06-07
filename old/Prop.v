Require Export Poly.

Check (2 + 2 = 4).

Check (ble_nat 3 2 = false).

Check (2 + 2 = 5).

Theorem plus_2_2_is_4:
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact :
  Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true:
  plus_fact.
Proof. reflexivity. Qed.

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.
Check teen.

Definition true_for_zero (P:nat -> Prop) : Prop := P 0.

Definition true_for_n__true_for_Sn (P:nat -> Prop) (n:nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P:nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat -> Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat -> Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Check our_nat_induction.

Inductive good_day: day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof.
  apply gd_sun.
Qed.

Inductive day_before: day -> day -> Prop :=
| db_tue : day_before tuesday monday
| db_wed : day_before wednesday tuesday
| db_thu : day_before thursday wednesday
| db_fri : day_before friday thursday
| db_sat : day_before saturday friday
| db_sun : day_before sunday saturday
| db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
| fdfs_any : forall d:day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof.
  apply fdfs_any.
Qed.

Inductive ok_day: day -> Prop :=
|okd_gd :
   forall d,
     good_day d -> ok_day d
|okd_before:
   forall d1 d2,
     ok_day d2 -> day_before d2 d1 -> ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
             (okd_before thursday friday
                         (okd_before friday saturday
                                     (okd_gd saturday gd_sat)
                                     db_sat)
                         db_fri)
             db_thu.

Theorem okdw': ok_day wednesday.
Proof.
  apply okd_before with (d2:=thursday).
  apply okd_before with (d2:=friday).
  apply okd_before with (d2:=saturday).
  apply okd_gd. apply gd_sat.
  apply db_sat.
  apply db_fri.
  apply db_thu.
Qed.

Definition okd_before2 := forall d1 d2 d3,
  ok_day d3 ->
  day_before d2 d1 ->
  day_before d3 d2 ->
  ok_day d1.

Theorem okd_before2_vaild : okd_before2.
Proof.
  unfold okd_before2.
  intros.
  generalize dependent H0.
  apply okd_before.
  generalize dependent H1.
  apply okd_before.
  apply H.
Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
  fun (H : ok_day d3) =>
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_vaild.

Check nat_ind.

Theorem mult_0_r':
  forall n:nat, n * 0 = 0.
Proof.
  apply nat_ind.
  Case "0". reflexivity.
  Case "S". simpl. intros n IHn. apply IHn.
Qed.

Theorem plus_one_r':
  forall n:nat, n + 1 = S n.
Proof.
  apply nat_ind.
  Case "0".
  simpl. reflexivity.
  Case "S".
  simpl. intros n IHn. apply eq_remove_S. apply IHn.
Qed.

Inductive yesno: Type :=
| yes: yesno
| no: yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist: Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| ncons1 : natlist1 -> nat -> natlist1.

Check natlist1_ind.

Inductive ExSet : Type :=
| con1 : forall b:bool, ExSet
| con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.

Check tree_ind.

Inductive mytype (X:Type) : Type :=
| constr1: X -> mytype X
| constr2: nat -> mytype X
| constr3: mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y:Type) : Type :=
| bar: X -> foo X Y
| baz: Y -> foo X Y
| quux: (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.

Check foo'_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r': nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' :
  forall n:nat, P_m0r n.
Proof.
  apply nat_ind.
  Case "n = 0". reflexivity.
  Case "n = S n".
  unfold P_m0r. simpl. intros n' IHn'.
  apply IHn'.
Qed.

Inductive ev : nat -> Prop :=
| ev_0: ev 0
| ev_SS: forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev':
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Print four_ev'.

Definition four_ev: ev 4 := ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_plus4':
  forall n, ev n -> ev (4 + n).
Proof.
  apply ev_ind.
 (* Case "n=0". *)
  simpl. apply four_ev.
  (* Case "n = S n". *)
  simpl.
  intros.
  apply ev_SS.
  apply H0.
Qed.

Print ev_plus4'.

Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  ev_ind (fun n : nat => ev (4 + n)) four_ev
         (fun (n : nat) (_ : ev n) (H0 : ev (S (S (S (S n))))) =>
            ev_SS (S (S (S (S n)))) H0).

Theorem double_even: forall n, ev (double n).
Proof.
  intros.
  induction n.
  simpl. apply ev_0.
  simpl. apply ev_SS. apply IHn.
Qed.

Print double_even.

Theorem ev_minus2:
  forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem ev_minus2_n:
  forall n, ev n -> ev (pred (pred n)).
  intros n E.
  destruct n as [| n'].
  Case "E = n". simpl. apply E.
  Case "E = S n". simpl.
  Restart.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem ev_even:
  forall n, ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
  unfold even. reflexivity.
  Case "E = ev_SS n' E'".
  unfold even. apply IHE'.
Qed.

Theorem ev_even_n:
  forall n, ev n -> even n.
Proof.
  intros n E. induction n as [| n' ].
  unfold even. simpl. reflexivity.
  unfold even.
Admitted.

Theorem ev_sum:
  forall n m, ev n -> ev m -> ev (n+m).
  intros n m En Em.
  induction En as [|n' En'].
  simpl. apply Em.
  simpl. apply ev_SS. apply IHEn'.
Qed.

Theorem SSev_ev_firsttry:
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
Admitted.

Theorem SSev_even:
  forall n, ev (S (S n)) -> ev n.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem SSSSev_even:
  forall n, ev (S (S (S (S n)))) -> ev n.
  intros n E.
  inversion E as [| n' E'].
  apply SSev_even.
  apply E'.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H as [| n' H'].
  inversion H'.
  inversion H2.
Qed.

Theorem ev_minus2':
  forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

Theorem ev_ev_even:
  forall n m, ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hn Hm.
  induction Hm.
  apply Hn.
  apply IHHm.
  apply SSev_even.
  apply Hn.
Qed.

Theorem ev_plus_plus:
  forall n m p, ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p H.
  apply ev_ev_even.
  rewrite plus_swap. rewrite <- plus_assoc.
  rewrite plus_swap. rewrite plus_assoc.
  apply ev_sum. apply H.
  SearchAbout (_ + _).
  rewrite <- double_plus. apply double_even.
Qed.

Inductive MyProp : nat -> Prop :=
| MyProp1: MyProp 4
| MyProp2: forall n:nat, MyProp n -> MyProp (4 + n)
| MyProp3: forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3.
  simpl. assert(12=4+8) as H12.
  Case "Proof of assertion.". reflexivity.
  rewrite H12.
  apply MyProp2.
  assert(8=4+4) as H8.
  Case "Proof of assertion.". reflexivity.
  rewrite H8.
  apply MyProp2.
  apply MyProp1.
Qed.

Theorem MyProp_0: MyProp 0.
Proof.
  apply MyProp3. simpl.
  apply MyProp3. simpl.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo :
  forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros.
  rewrite <- plus_one_r'.
  rewrite <- plus_one_r'.
  rewrite <- plus_assoc.
  simpl.
  rewrite <- plus_comm.
  apply MyProp3.
  rewrite plus_assoc.
  rewrite <- plus_comm.
  simpl.
  rewrite <- plus_comm.
  apply MyProp2.
  apply H.
Qed.

Theorem MyProp_ev :
  forall n:nat, ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [|n' E'].
  Case "E = ev_0".
  apply MyProp_0.
  Case "E = ev_SS n' E'".
  apply MyProp_plustwo.
  apply IHE'.
Qed.

(*
非形式的な証明.
定理: 任意の自然数nにおいて,ev nならばMyProp nが成り立つ
証明:
   n = 0のとき,MyProp 0は補題MyProp_0で成立
   n = S (S n')のとき,MyProp n'が成立すると仮定すると,
   MyProp  S (S n')は,MyProp_plustwoが成立するので,帰納法により定理は成立する.
 *)

Theorem ev_MyProp:
  forall n:nat, MyProp n -> ev n.
Proof.
  intros n P.
  induction P.
  Case "n = 4".
  apply four_ev.
  Case "n = 4 + n'".
  apply ev_plus4.
  apply IHP.
  Case "n = 2 + n'".
  simpl in IHP.
  apply SSev_even.
  apply IHP.
Qed.

Theorem plus_assoc' :
  forall n m p: nat, n+(m+p)=(n+m)+p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n=0".
  simpl. reflexivity.
  Case "n=S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm' :
  forall n m : nat, n + m = m + n.
Proof.
  induction n as [|n'].
  Case "n=0".
  intro m. rewrite plus_0_r. simpl. reflexivity.
  Case "n=S n'".
  intro m. simpl.
  rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem plus_comm'' :
  forall n m: nat, n + m = m + n.
  induction m as [| m'].
  Case "m = 0".
  simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m".
  simpl. rewrite <- IHm'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Check ev_ind.

Theorem ev_even':
  forall n:nat,ev n -> even n.
Proof.
  apply ev_ind.
  Case "ev_0". unfold even. reflexivity.
  Case "ev_SS". intros n' E' IHE'. unfold even. apply IHE'.
Qed.

Check list_ind.
Check MyProp_ind.

Theorem ev_MyProp':
  forall n:nat, MyProp n -> ev n.
Proof.
  apply MyProp_ind.
  Case "n = 4".
  apply four_ev.
  Case "n = 4 + n'".
  intros.
  apply ev_plus4.
  apply H0.
  Case "n = 2 + n".
  intros.
  simpl in H0.
  apply SSev_even.
  apply H0.
Qed.

Print ev_plus4'.

Print MyProp_ev.

Definition MyProp_ev' :
  forall n:nat, ev n -> MyProp n :=
  fun (n : nat) (E : ev n) =>
    ev_ind (fun n : nat => MyProp n) MyProp_0
           (fun (n' : nat) (_ : ev n') (H : MyProp n') => MyProp_plustwo n' H) n E.

Print ev_MyProp.
Print MyProp_ind.

Definition ev_MyProp'' :
  forall n : nat, MyProp n -> ev n :=
  fun (n : nat) (P : MyProp n) =>
    MyProp_ind (fun m : nat => ev m) four_ev
               (fun (m : nat) (_ : MyProp m) (H : ev m) => ev_plus4 m H)
               (fun (m : nat) (_ : MyProp (2 + m)) (H : ev (2 + m)) => SSev_even m H) n P.

Module Test.
Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
Check foo_ind.
End Test.


Inductive pal {X :Type}: list X -> Prop :=
| c0 : pal []
| c1 : forall n:X, pal [n]
| c2 : forall (n:X) (l:list X), pal l -> pal (n :: (snoc l n)).

Theorem pal_ref :
  forall {X:Type} (l:list X), pal (l ++ rev l).
  intros.
  induction l.
  Case "l = []".
  simpl.
  apply c0.
  Case "l = x::l'".
  simpl.
  rewrite <- snoc_with_append.
  apply c2.
  apply IHl.
Qed.

Lemma rev_involutive:
  forall {X:Type} (l:list X), rev (rev l) = l.
Proof.
  intros.
  induction l as [| n l'].
  Case "l=[]".
  simpl.
  reflexivity.
  Case "l=[n::l]".
  assert (H1:forall {X:Type} (n: X) (l:list X), rev (snoc l n) = n::rev l).
  intros.
  induction l as [|n0' l0'].
  SCase "l0=[]".
  simpl.
  reflexivity.
  SCase "l0=n0::l0'".
  simpl.
  rewrite -> IHl0'.
  simpl.
  reflexivity.
  simpl.
  rewrite->H1.
  rewrite->IHl'.
  reflexivity.
Qed.

Theorem pal_id_rev:
  forall {X:Type} (l:list X), pal l -> l = rev l.
Proof.
  intros.
  induction H.
  Case "l = []".
  simpl.
  reflexivity.
  Case "l = [n]".
  simpl.
  reflexivity.
  Case "l = [n::l::n]".
  rewrite IHpal.
  simpl.
  rewrite rev_snoc.
  simpl.
  rewrite -> rev_involutive.
  rewrite <- IHpal.
  reflexivity.
Qed.

Inductive subseq : list nat -> list nat -> Prop :=
| subseq_c1 : forall l, subseq [] l
| subseq_c2 : forall sl l n m, subseq (n::sl) l -> subseq (n::sl) (m::l)
| subseq_c3 : forall sl l n, subseq sl l -> subseq (n::sl) (n::l).

Check subseq.
Check (subseq [1,2,3] [1,2,3]).
Check subseq_c3.

Example subseq_ex1:
  subseq [] [1,2,3].
Proof.
  apply subseq_c1.
Qed.

Example subseq_ex2:
  subseq [1] [1,2,3].
Proof.
  apply subseq_c3.
  apply subseq_c1.
Qed.

Example subseq_ex3:
  subseq [1,2,3] [1,2,3].
Proof.
  apply subseq_c3.
  apply subseq_c3.
  apply subseq_c3.
  apply subseq_c1.
Qed.

Example subseq_ex4:
  subseq [1,2,3] [1,2,7,3].
Proof.
  apply subseq_c3.
  apply subseq_c3.
  apply subseq_c2.
  apply subseq_c3.
  apply subseq_c1.
Qed.

Example subseq_ex5:
  subseq [1,2,3] [5,6,1,9,9,2,7,3,8].
Proof.
  apply subseq_c2.
  apply subseq_c2.
  apply subseq_c3.
  apply subseq_c2.
  apply subseq_c2.
  apply subseq_c3.
  apply subseq_c2.
  apply subseq_c3.
  apply subseq_c1.
Qed.

Theorem subseq_involutive:
  forall s1 s2:list nat,  s1 s2 -> subseq s1 s2.
Proof.
  
  
Module Foo_Ind_principle.
  Inductive foo (X: Set) (Y: Set) : Set :=
  | foo1 : X -> foo X Y
  | foo2 : Y -> foo X Y
  | foo3 : foo X Y -> foo X Y.
  Check foo_ind.
End Foo_Ind_principle.

Module R.

  Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.

  Check R.
  Check (R 1 [1,2,1,0]).
  Check (R 2 [1,0]).
  Check (R 6 [3,2,1,0]).

  Theorem r_1_list_1_2_1_0:
    R 1 [1,2,1,0].
  Proof.
    apply c3.
    apply c2.
    apply c3.
    apply c3.
    apply c2.
    apply c2.
    apply c2.
    apply c1.
  Qed.

  Theorem r_2_list_1_0:
    R 2 [1,0].
  Proof.
    apply c2.
    apply c2.
    apply c1.
  Qed.
End R.