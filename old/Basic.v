
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity.  Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true ) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true ) = true.
Proof. simpl. reflexivity.  Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb b1 (andb b2 b3).

Example test_andb31: (andb3 true true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Check (negb true).

Check negb.

Module Playground1.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  
  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.
End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.
  
  Eval simpl in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Fixpoint minus (n m:nat) : nat :=
    match n, m with
      | O   , _  => O
      | S _ , O  => n
      | S n', S m' => minus n' m'
    end.

  Eval simpl in (minus (S (S (S O))) (S (S O))).
  Eval simpl in (minus (S (S O)) (S (S (S O)))).

End Playground2.

Fixpoint exp (base power : nat): nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
  simpl.
  reflexivity.
Qed.

Notation "x + y" := (plus  x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult  x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m:nat) : bool :=
  match n with
    |O => match m with
            | O => true
            | S m' => false
          end
    | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
              end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
          | O => false
          | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n: forall n:nat, 0 + n = n.
Proof. simpl. reflexivity. Qed.

Eval simpl in (forall n:nat, n + 0 = n).

Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_O_n'' : forall n:nat, 0+n=n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise :
  forall n m o:nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_l_plus:
  forall n m:nat, (0+n)*m = n*m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_1_plus:
  forall n m:nat, (1 + n) * m = m + (n * m).
  intros n m.
  rewrite -> plus_1_l.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0 :
  forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
  intro n.
  destruct n as [|n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : 
  forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1:
  forall n : nat, beq_nat 0 (n+1) = false.
Proof.
  intros n.
  destruct n as [|n'].
  reflexivity.
  reflexivity.
Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1:
  forall b c : bool, andb b c = true -> b = true.
  intros b c H.
  destruct b.
  Case "b = true".
  reflexivity.
  Case "b = false".
  rewrite <- H.
  reflexivity.
Qed.

Theorem andb_true_elim2:
  forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
  reflexivity.
  Case "c = false".
  rewrite <- H.
  destruct b.
  SCase "b = true".
  reflexivity.
  SCase "b = false".
  reflexivity.
Qed.

Theorem plus_0_r :
  forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag :
  forall n, minus n n = 0.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  rewrite -> plus_0_r.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite <- plus_n_Sm.
  rewrite -> IHn'.
  reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus :
  forall n, double n = n + n .
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem beq_nat_refl :
  forall n : nat, true = beq_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  Case "Proof of assertion".
  rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H1: n + (m + p) = (n + m) + p).
  Case "Proof of assertion H1".
  rewrite -> plus_assoc.
  reflexivity.
  assert (H2: m + (n + p) = (m + n) + p).
  Case "Proof of assertion H2".
  rewrite -> plus_assoc.
  reflexivity.
  assert (H3: n + m = m + n).
  Case "Proof of assertion H3".
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H1.
  rewrite -> H2.
  rewrite -> H3.
  reflexivity.
Qed.

Theorem mult_comm :
  forall m n : nat, m * n = n * m.
Proof.
  assert (mult_n_Sm: forall n m : nat, n + n * m = n * (S m)).
  intros n m.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite <- IHn'.
  rewrite <- plus_swap.
  reflexivity.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  rewrite -> mult_0_r.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite <- mult_n_Sm.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b as [|b'].
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H1.
  induction p as [|p'].
  simpl.
  rewrite -> H1.
  reflexivity.
  simpl.
  rewrite -> IHp'.
  reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  assert (plus_0_r: forall m : nat, m + 0 = m).
  induction m as [|m'].
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHm'.
  reflexivity.
  rewrite -> plus_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c.
  destruct b as [|b'].
  Case "b = true".
  destruct c as [|c'].
  SCase "c = true".
  simpl.
  reflexivity.
  SCase "c = false".
  simpl.
  reflexivity.
  Case "b = false".
  destruct c as [|c'].
  SCase "c = true".
  simpl.
  reflexivity.
  SCase "c = false".
  simpl.
  reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite -> mult_plus_distr_r.
  reflexivity.
Qed.

Theorem plus_swap' :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (m + n) with (n + m).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(** binary **)

Module Binary.

  Inductive bin : Type :=
  | Zero  : bin
  | Twice : bin -> bin
  | TwicePlusOne : bin -> bin.

Fixpoint inc (b:bin) : bin :=
  match b with
      | Zero => TwicePlusOne Zero
      | Twice b' => TwicePlusOne b'
      | TwicePlusOne b' => Twice (inc b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
      | Zero => O
      | Twice b' => 2 * (bin_to_nat b')
      | TwicePlusOne b' => 1 + 2 * (bin_to_nat b')
  end.

Check inc. 
Eval simpl in (inc Zero).
Eval simpl in (inc (inc Zero)).
Eval simpl in bin_to_nat (inc (inc (inc Zero))).
Eval simpl in (inc (inc (inc (inc Zero)))).
Eval simpl in bin_to_nat (inc (inc (inc (inc Zero)))).

Theorem bin_nat_comm: 
  forall b:bin, bin_to_nat (inc b) = 1 + (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b1|b2].
  Case "b = Zero".
  simpl.
  reflexivity.
  Case "b = Twice b'".
  simpl.
  reflexivity.
  Case "b = TwicePlusOne b'".
  simpl.
  rewrite -> plus_0_r.
  rewrite -> plus_0_r.
  rewrite -> IHb2.
  simpl.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin:=
  match n with
    | O => Zero
    | S n' => inc (nat_to_bin n')
  end.

Eval simpl in (inc Zero).
Eval simpl in nat_to_bin 1.
Eval simpl in (inc (inc Zero)).
Eval simpl in nat_to_bin 2.
Eval simpl in (inc (inc (inc Zero))).
Eval simpl in bin_to_nat (nat_to_bin 3).

Theorem nat_bin_comm:
  forall n:nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> bin_nat_comm.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

End Binary.